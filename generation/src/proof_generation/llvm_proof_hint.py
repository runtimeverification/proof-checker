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
class LLVMRuleEvent(LLVMStepEvent):
    rule_ordinal: int
    substitution: tuple[tuple[str, kore.Pattern], ...]


@dataclass
class LLVMFunctionEvent(LLVMStepEvent):
    name: str
    relative_position: str
    args: tuple[kore.Pattern, ...]  # kore term arguments only


@dataclass
class LLVMHookEvent(LLVMStepEvent):
    name: str
    args: tuple[kore.Pattern, ...]  # kore term arguments only
    result: kore.Pattern


@dataclass
class LLVMRewriteTrace:
    pre_trace: tuple[LLVMStepEvent | kore.Pattern, ...]
    initial_config: kore.Pattern
    trace: tuple[LLVMStepEvent | kore.Pattern, ...]

    @staticmethod
    def parse(input: bytes, debug: bool = False) -> LLVMRewriteTrace:
        parser = LLVMRewriteTraceParser(input)
        ret = parser.read_execution_hint(debug)
        assert parser.eof()
        return ret


EXPECTED_HINTS_VERSION: Final = 1


class LLVMRewriteTraceParser:
    """
    proof_trace ::= header step_event* config events*
    header      ::= "HINT" <4-byte version number>
    step_event  ::= hook | function | rule
    event       ::= step_event | config
    hook        ::= WORD(0xAA) name argument* WORD(0xBB) kore_term
    function    ::= WORD(0xDD) name location argument* WORD(0x11)
    rule        ::= WORD(0x22) ordinal arity variable*
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
    side_condn_sentinel: Final = bytes([0xEE] * 8)
    kore_term_prefix: Final = b'\x7FKORE'
    null_byte: Final = b'\x00'

    def __init__(self, input: bytes):
        self.input = input
        self.trace: list[tuple[int, LLVMStepEvent | kore.Pattern]] = []
        self.init_config_pos = 0
        self.entry_index = 0

    def read_execution_hint(self, debug: bool) -> LLVMRewriteTrace:
        # read the header
        version = self.read_header()
        assert version == EXPECTED_HINTS_VERSION, f'Expected version {EXPECTED_HINTS_VERSION}, found version {version}'

        # read the prefix trace (step events)
        while not self.peek(self.config_sentinel):
            self.read_step_event()

        # read the initial configuration
        self.init_config_pos = len(self.trace)
        self.initial_config = self.read_config()

        # read the rest of the trace (all events)
        while not self.eof():
            self.read_event()

        return self.build_llvm_trace(debug)

    def read_header(self) -> int:
        self.skip_constant(b'HINT')
        return self.read_uint(32)

    def build_llvm_trace(self, debug: bool) -> LLVMRewriteTrace:
        self.trace.sort(key=lambda e: e[0])
        prefix = self.trace[: self.init_config_pos]
        postfix = self.trace[self.init_config_pos + 1 :]

        if debug:
            self.print_trace(prefix, postfix)

        pre_trace = tuple([event for (i, event) in prefix])
        _, initial_config = self.trace[self.init_config_pos]
        trace = tuple([event for (i, event) in postfix])

        assert isinstance(initial_config, kore.Pattern)
        return LLVMRewriteTrace(pre_trace, initial_config, trace)

    def print_trace(
        self,
        prefix: list[tuple[int, LLVMStepEvent | kore.Pattern]],
        postfix: list[tuple[int, LLVMStepEvent | kore.Pattern]],
    ) -> None:
        for i, e in prefix:
            if isinstance(e, LLVMRuleEvent):
                print(f'{i} rule {e.rule_ordinal}')
            elif isinstance(e, LLVMFunctionEvent):
                print(f'{i} function {e.name}')
            elif isinstance(e, LLVMHookEvent):
                print(f'{i} hook {e.name}')
            else:
                assert isinstance(e, kore.Pattern)
                print(f'{i} config')
        print(f'init config at {self.init_config_pos}')
        for i, e in postfix:
            if isinstance(e, LLVMRuleEvent):
                print(f'{i} rule {e.rule_ordinal}')
            elif isinstance(e, LLVMFunctionEvent):
                print(f'{i} function {e.name}')
            elif isinstance(e, LLVMHookEvent):
                print(f'{i} hook {e.name}')
            else:
                assert isinstance(e, kore.Pattern)
                print(f'{i} config')

    def read_step_event(self) -> None:
        if self.peek(self.hook_event_sentinel):
            self.read_hook()
        elif self.peek(self.func_event_sentinel):
            self.read_function()
        else:
            self.read_rule()

    def read_event(self) -> None:
        if self.peek(self.config_sentinel):
            self.read_config()
        else:
            self.read_step_event()

    def read_hook(self) -> None:
        self.skip_constant(self.hook_event_sentinel)
        name = self.read_c_string()
        saved_index = self.entry_index
        self.entry_index += 1

        while not self.end_of_arguments():
            self.read_argument()

        self.skip_constant(self.hook_res_sentinel)
        result = self.read_kore()

        # TODO: add args
        hook_event = LLVMHookEvent(name=name, args=(), result=result)
        self.add_to_trace(saved_index, hook_event)

    def read_function(self) -> None:
        self.skip_constant(self.func_event_sentinel)
        name = self.read_c_string()
        position = self.read_c_string()
        saved_index = self.entry_index
        self.entry_index += 1

        while not self.end_of_arguments():
            self.read_argument()

        self.skip_constant(self.func_end_sentinel)

        # TODO: add args
        func_event = LLVMFunctionEvent(name=name, relative_position=position, args=())
        self.add_to_trace(saved_index, func_event)

    def read_rule(self) -> None:
        self.skip_constant(self.rule_event_sentinel)
        ordinal = self.read_uint(64)
        arity = self.read_uint(64)
        saved_index = self.entry_index
        self.entry_index += 1

        substitution: tuple[tuple[str, kore.Pattern], ...] = ()
        for _ in range(arity):
            variable_name = self.read_variable_name()
            target = self.read_tailed_term()
            substitution = substitution + ((variable_name, target),)

        # TODO: add args
        rule_event = LLVMRuleEvent(rule_ordinal=ordinal, substitution=substitution)
        self.add_to_trace(saved_index, rule_event)

    def read_config(self) -> kore.Pattern:
        self.skip_constant(self.config_sentinel)
        config = self.read_tailed_term()
        self.add_to_trace(self.entry_index, config)
        self.entry_index += 1
        return config

    def add_to_trace(self, index: int, event: LLVMStepEvent | kore.Pattern) -> None:
        self.trace.append((index, event))

    def read_argument(self) -> None:
        if self.peek(self.kore_term_prefix):
            self.read_kore()
        else:
            self.read_step_event()

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


# A driver for local testing
if __name__ == '__main__':

    def load(fn: str) -> bytes:
        with open(fn, 'rb') as f:
            return f.read()

    data = load(sys.argv[1])
    LLVMRewriteTrace.parse(data, debug=True)
