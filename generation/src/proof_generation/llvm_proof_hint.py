from __future__ import annotations

import struct
import sys
from dataclasses import dataclass
from typing import TYPE_CHECKING

import pyk.kllvm.load  # noqa: F401
import pyk.kore.syntax as kore
from pyk.kllvm import ast as kllvm_kore
from pyk.kllvm.convert import llvm_to_pattern

if TYPE_CHECKING:
    from typing import Final


@dataclass
class LLVMStepEvent:
    pass


@dataclass
class LLVMRewriteEvent(LLVMStepEvent):
    rule_ordinal: int
    substitution: tuple[tuple[str, kore.Pattern], ...]


@dataclass
class LLVMRuleEvent(LLVMRewriteEvent):
    pass


@dataclass
class LLVMSideCondEvent(LLVMRewriteEvent):
    pass


@dataclass
class LLVMFunctionEvent(LLVMStepEvent):
    name: str
    relative_position: str
    args: tuple[Argument, ...]


@dataclass
class LLVMHookEvent(LLVMStepEvent):
    name: str
    relative_position: str
    args: tuple[Argument, ...]
    result: kore.Pattern


@dataclass
class LLVMRewriteTrace:
    pre_trace: tuple[Argument, ...]
    initial_config: kore.Pattern
    trace: tuple[Argument, ...]

    @staticmethod
    def parse(input: bytes, debug: bool = False) -> LLVMRewriteTrace:
        parser = LLVMRewriteTraceParser(input)
        ret = parser.read_execution_hint(debug)
        assert parser.eof()
        return ret


Argument = LLVMStepEvent | kore.Pattern

EXPECTED_HINTS_VERSION: Final = 3


class LLVMRewriteTraceParser:
    """
    proof_trace ::= header step_event* config events*
    header      ::= "HINT" <4-byte version number>
    step_event  ::= hook | function | rule | side_cond
    event       ::= step_event | config
    hook        ::= WORD(0xAA) name location argument* WORD(0xBB) kore_term
    function    ::= WORD(0xDD) name location argument* WORD(0x11)
    rule        ::= WORD(0x22) match
    side_cond   ::= WORD(0xEE) match
    match       ::= ordinal arity variable*
    config      ::= WORD(0xFF) tailed_term
    argument    ::= step_event | kore_term
    variable    ::= name tailed_term
    tailed_term ::= kore_term WORD(0xCC)

    name        ::= string
    location    ::= string
    ordinal     ::= uint64
    arity       ::= uint64
    string      ::= <c-style null terminated string>
    uint64      ::= <64-bit unsigned little endian integer>
    """

    config_sentinel: Final = bytes([0xFF] * 8)
    kore_end_sentinel: Final = bytes([0xCC] * 8)
    func_event_sentinel: Final = bytes([0xDD] * 8)
    func_end_sentinel: Final = bytes([0x11] * 8)
    hook_event_sentinel: Final = bytes([0xAA] * 8)
    hook_res_sentinel: Final = bytes([0xBB] * 8)
    rule_event_sentinel: Final = bytes([0x22] * 8)
    side_cond_event_sentinel: Final = bytes([0xEE] * 8)
    kore_term_prefix: Final = b'\x7FKORE'
    null_byte: Final = b'\x00'

    def __init__(self, input: bytes):
        self.input = input
        self.pre_trace: list[LLVMStepEvent] = []
        self.init_config_pos = 0
        self.trace: list[Argument] = []

    def read_execution_hint(self, debug: bool) -> LLVMRewriteTrace:
        # read the header
        version = self.read_header()
        assert version == EXPECTED_HINTS_VERSION, f'Expected version {EXPECTED_HINTS_VERSION}, found version {version}'

        # read the prefix trace (step events)
        while not self.peek(self.config_sentinel):
            self.pre_trace.append(self.read_step_event())

        # read the initial configuration
        self.init_config_pos = len(self.pre_trace)
        self.initial_config = self.read_config()

        # read the rest of the trace (all events)
        while not self.eof():
            self.trace.append(self.read_event())

        if debug:
            self.dump_trace()

        return LLVMRewriteTrace(tuple(self.pre_trace), self.initial_config, tuple(self.trace))

    def read_header(self) -> int:
        self.skip_constant(b'HINT')
        return self.read_uint(32)

    def read_step_event(self) -> LLVMStepEvent:
        if self.peek(self.hook_event_sentinel):
            return self.read_hook()
        elif self.peek(self.func_event_sentinel):
            return self.read_function()
        elif self.peek(self.rule_event_sentinel):
            return self.read_rule()
        elif self.peek(self.side_cond_event_sentinel):
            return self.read_side_cond()
        else:
            raise ValueError(f'Unexpected input: {self.input.hex()}')

    def read_event(self) -> Argument:
        if self.peek(self.config_sentinel):
            return self.read_config()
        else:
            return self.read_step_event()

    def read_hook(self) -> LLVMHookEvent:
        self.skip_constant(self.hook_event_sentinel)
        name = self.read_c_string()
        position = self.read_c_string()

        args = []
        while not self.end_of_arguments():
            args.append(self.read_argument())

        self.skip_constant(self.hook_res_sentinel)
        result = self.read_kore()
        return LLVMHookEvent(name=name, relative_position=position, args=tuple(args), result=result)

    def read_function(self) -> LLVMFunctionEvent:
        self.skip_constant(self.func_event_sentinel)
        name = self.read_c_string()
        position = self.read_c_string()

        args = []
        while not self.end_of_arguments():
            args.append(self.read_argument())

        self.skip_constant(self.func_end_sentinel)
        return LLVMFunctionEvent(name=name, relative_position=position, args=tuple(args))

    def read_rule(self) -> LLVMRuleEvent:
        self.skip_constant(self.rule_event_sentinel)
        ordinal, substitution = self.read_match()
        return LLVMRuleEvent(rule_ordinal=ordinal, substitution=substitution)

    def read_side_cond(self) -> LLVMSideCondEvent:
        self.skip_constant(self.side_cond_event_sentinel)
        ordinal, substitution = self.read_match()
        return LLVMSideCondEvent(rule_ordinal=ordinal, substitution=substitution)

    def read_match(self) -> tuple[int, tuple[tuple[str, kore.Pattern], ...]]:
        ordinal = self.read_uint(64)
        arity = self.read_uint(64)

        substitution: tuple[tuple[str, kore.Pattern], ...] = ()
        for _ in range(arity):
            variable_name = self.read_variable_name()
            target = self.read_tailed_term()
            substitution = substitution + ((variable_name, target),)

        return ordinal, substitution

    def read_config(self) -> kore.Pattern:
        self.skip_constant(self.config_sentinel)
        return self.read_tailed_term()

    def read_argument(self) -> Argument:
        if self.peek(self.kore_term_prefix):
            return self.read_kore()
        else:
            return self.read_step_event()

    def read_tailed_term(self) -> kore.Pattern:
        raw_term = self.read_until(self.kore_end_sentinel)
        self.skip_constant(self.kore_end_sentinel)
        return self.to_kore(raw_term)

    def read_kore(self) -> kore.Pattern:
        # Kore term prefix: 5 bytes for b'\x7FKORE' + 6 bytes => 11-byte prefix
        # followed by an 8-byte uint64 => 19 bytes total
        kore_term_length = self.peek_uint64_at(11)
        total_length = 11 + 8 + kore_term_length
        raw_term = self.input[:total_length]
        self.skip(total_length)
        return self.to_kore(raw_term)

    def to_kore(self, raw_term: bytes) -> kore.Pattern:
        llvm_pattern = kllvm_kore.Pattern.deserialize(raw_term)
        assert llvm_pattern, ('Could not deserialize binary kore.', input)
        return llvm_to_pattern(llvm_pattern)

    def read_variable_name(self) -> str:
        return self.read_c_string()

    def read_c_string(self) -> str:
        ret = str(self.read_until(self.null_byte), 'ascii')
        self.skip_constant(self.null_byte)
        return ret

    def skip_constant(self, constant: bytes) -> None:
        assert self.input[: len(constant)] == constant
        self.input = self.input[len(constant) :]

    def read_uint(self, size: int) -> int:
        assert size in {32, 64}
        little_endian = {32: '<I', 64: '<Q'}
        index = size // 8
        raw = self.input[:index]
        self.input = self.input[index:]
        return struct.unpack(little_endian[size], raw)[0]

    def read_until(self, constant: bytes) -> bytes:
        index = self.input.find(constant)
        ret = self.input[:index]
        self.input = self.input[index:]
        return ret

    def peek_uint64_at(self, idx: int) -> int:
        length = 8
        raw = self.input[idx : idx + length]
        little_endian_long_long = '<Q'
        return struct.unpack(little_endian_long_long, raw)[0]

    def peek(self, cst: bytes) -> bool:
        return self.input[: len(cst)] == cst

    def skip(self, n: int) -> None:
        self.input = self.input[n:]

    def eof(self) -> bool:
        return len(self.input) == 0

    def end_of_arguments(self) -> bool:
        return self.peek(self.func_end_sentinel) or self.peek(self.hook_res_sentinel)

    def dump_trace(
        self,
        show_terms: bool = False,
    ) -> None:
        def dump(text: str, depth: int, end: str = '\n') -> None:
            print(f'{"  " * depth}{text}', end=end)

        def dump_event(event: Argument, depth: int, top: bool = False) -> None:
            if isinstance(event, LLVMRuleEvent):
                dump(f'Rule: {event.rule_ordinal} {len(event.substitution)}', depth)
                for v, t in event.substitution:
                    dump(f'{v} = {t if show_terms else "[kore]"}', depth + 1)
            elif isinstance(event, LLVMSideCondEvent):
                dump(f'Side Condition: {event.rule_ordinal} {len(event.substitution)}', depth)
                for v, t in event.substitution:
                    dump(f'{v} = {t if show_terms else "[kore]"}', depth + 1)
            elif isinstance(event, LLVMFunctionEvent):
                dump(f'Function: {event.name} @ {event.relative_position}', depth)
                for arg in event.args:
                    dump_event(arg, depth + 1)
            elif isinstance(event, LLVMHookEvent):
                dump(f'Hook: {event.name} @ {event.relative_position}', depth)
                for arg in event.args:
                    dump_event(arg, depth + 1)
                dump(f'Result: {event.result if show_terms else "[kore]"}', depth + 1)
            else:
                assert isinstance(event, kore.Pattern)
                dump(f'{"Config" if top else "Term"}: {event if show_terms else "[kore]"}', depth)

        depth = 0
        for step_event in self.pre_trace:
            dump_event(step_event, depth, top=True)
        dump(f'Init config: {self.initial_config if show_terms else "[kore]"}', depth)
        for event in self.trace:
            dump_event(event, depth, top=True)


# A driver for local testing
if __name__ == '__main__':

    def load(fn: str) -> bytes:
        with open(fn, 'rb') as f:
            return f.read()

    data = load(sys.argv[1])
    LLVMRewriteTrace.parse(data, debug=True)
