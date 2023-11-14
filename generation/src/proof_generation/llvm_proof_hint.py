from __future__ import annotations

import struct
from dataclasses import dataclass
from typing import TYPE_CHECKING

# TODO: drop test modules
import pyk.kllvm.load  # noqa: F401
import sys

from pyk.kllvm import ast as kllvm_kore
from pyk.kllvm.convert import llvm_to_kore

if TYPE_CHECKING:
    from typing import Final

    from pyk.kore.syntax import Pattern


@dataclass
class LLVMStepEvent:
    pass


@dataclass
class LLVMRuleEvent(LLVMStepEvent):
    rule_ordinal: int
    substitution: tuple[tuple[str, Pattern], ...]


@dataclass
class LLVMFunctionEvent(LLVMStepEvent):
    name: str
    relative_position: str
    args: tuple[Pattern]  # kore term arguments


@dataclass
class LLVMHookEvent(LLVMStepEvent):
    name: str
    args: tuple[Pattern]  # kore term arguments
    result: Pattern


@dataclass
class LLVMRewriteTrace:
    pre_trace: tuple[LLVMStepEvent, ...]
    initial_config: Pattern
    trace: tuple[LLVMStepEvent | Pattern, ...]

    @staticmethod
    def parse(input: bytes) -> LLVMRewriteTrace:
        parser = LLVMRewriteTraceParser(input)
        ret = parser.read_proof_trace()
        assert parser.eof()
        return ret


class LLVMRewriteTraceParser:
    """
    proof_trace ::= step_event* config events*
    step_event  ::= hook | function | rule
    event       ::= step_event | config
    hook        ::= WORD(0xAA) name argument* WORD(0xBB) kore_term
    function    ::= WORD(0xDD) name location argument* WORD(0x11)
    rule        ::= ordinal arity variable*
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
    side_condn_sentinel: Final = bytes([0xEE] * 8)
    kore_term_prefix: Final = b'\x7FKORE'

    def __init__(self, input: bytes):
        self.input = input
        self.pre_trace: tuple[LLVMStepEvent, ...] = ()
        self.initial_config: Pattern | None = None
        self.trace: tuple[LLVMStepEvent, ...] = ()

    def read_proof_trace(self) -> LLVMRewriteTrace:
        # read the prefix trace (step events)
        while not self.peek(self.config_sentinel):
            self.read_step_event(True)

        # read the initial configuration
        self.initial_config = self.read_config(is_initial=True)

        # read the rest of the trace (all events)
        while not self.eof():
            self.read_event()

        # TODO: return proper trace
        return LLVMRewriteTrace((), self.initial_config, ())

    def read_step_event(self, is_prefix: bool = False) -> None:
        if self.peek(self.hook_event_sentinel):
            self.read_hook(is_prefix)
        elif self.peek(self.func_event_sentinel):
            self.read_function(is_prefix)
        else:
            self.read_rule(is_prefix)

        #         trace = trace + (next,)
        #         pre_trace = pre_trace + (next,)

    def read_event(self, is_prefix: bool = False) -> None:
        if self.peek(self.config_sentinel):
            self.read_config()
        else:
            self.read_step_event(is_prefix)

    def read_hook(self, is_prefix: bool = False) -> None:
        self.skip_constant(self.hook_event_sentinel)
        name = self.read_c_string()
        print(f'hook: {name}')

        while not self.end_of_arguments():
            self.read_argument(is_prefix)

        self.skip_constant(self.hook_res_sentinel)
        result = self.read_kore()
        print(f'hook result: kore[]')

        # TODO: add args
        # hook_event = LLVMHookEvent(post_config=None, name=name, args=None, result=result)

        # TODO: add hook_event to the trace at the right position

    def read_function(self, is_prefix: bool = False) -> None:
        self.skip_constant(self.func_event_sentinel)
        name = self.read_c_string()
        position = self.read_c_string()
        print(f'function: {name} ({position})')

        while not self.end_of_arguments():
            self.read_argument(is_prefix)

        self.skip_constant(self.func_end_sentinel)

        # TODO: add func_event to the trace at the right position

    def read_rule(self, is_prefix: bool = False) -> None:
        ordinal = self.read_uint64()
        arity = self.read_uint64()
        print(f'rule: {ordinal} {arity}')

        substitution: tuple[tuple[str, Pattern], ...] = ()
        for _ in range(arity):
            variable_name = self.read_variable_name()
            target = self.read_tailed_term()
            print(f'  {variable_name} = kore[]')
            substitution = substitution + ((variable_name, target),)

        # TODO: add rule_event to the trace at the right position

    def read_config(self, is_initial: bool = False) -> Pattern:
        self.skip_constant(self.config_sentinel)
        config = self.read_tailed_term()
        if is_initial:
            self.initial_config = config
        else:
            # TODO: add config to the trace at the right position
            pass
        print('config: kore[]')
        return config


    def read_argument(self, is_prefix: bool = False) -> None:
        if self.peek(self.kore_term_prefix):
            self.read_kore()
            print('arg: kore[]')
        else:
            self.read_step_event(is_prefix)

    def read_tailed_term(self) -> Pattern:
        raw_term = self.read_until(self.kore_end_sentinel)
        self.skip_constant(self.kore_end_sentinel)
        return self.to_kore(raw_term)

    def read_kore(self) -> Pattern:
        kore_term_length = self.peak_uint64_at(11)
        total_length = 11 + 8 + kore_term_length
        raw_term = self.input[:total_length]
        self.skip(total_length)
        return self.to_kore(raw_term)

    def to_kore(self, raw_term: bytes) -> Pattern:
        llvm_pattern = kllvm_kore.Pattern.deserialize(raw_term)
        assert llvm_pattern, ('Could not deserialize binary kore.', input)
        return llvm_to_kore(llvm_pattern)

    def read_variable_name(self) -> str:
        return self.read_c_string()

    def read_c_string(self) -> str:
        ret = str(self.read_until(b'\x00'), 'ascii')
        self.skip_constant(b'\x00')
        return ret

    def skip_constant(self, constant: bytes) -> None:
        assert self.input[: len(constant)] == constant
        self.input = self.input[len(constant) :]

    def read_uint64(self) -> int:
        index = 8
        raw = self.input[:index]
        self.input = self.input[index:]
        little_endian_long_long = '<Q'
        return struct.unpack(little_endian_long_long, raw)[0]

    def read_until(self, constant: bytes) -> bytes:
        index = self.input.find(constant)
        ret = self.input[:index]
        self.input = self.input[index:]
        return ret

    def peak_uint64_at(self, idx: int) -> int:
        length = 8
        raw = self.input[idx:idx+length]
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

def load(fn):
    with open(fn, 'rb') as f:
        return f.read()

if __name__ == '__main__':
    data = load(sys.argv[1])
    LLVMRewriteTrace.parse(data)
