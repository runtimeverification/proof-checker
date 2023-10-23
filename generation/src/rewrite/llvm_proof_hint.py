from __future__ import annotations

import struct
from dataclasses import dataclass
from typing import TYPE_CHECKING

from pyk.kllvm import ast as kllvm_kore
from pyk.kllvm.convert import llvm_to_kore

if TYPE_CHECKING:
    from typing import Final

    from pyk.kore.syntax import Pattern


@dataclass
class LLVMRewriteStep:
    rule_ordinal: int
    substitution: tuple[tuple[str, Pattern], ...]
    post_config: Pattern


@dataclass
class LLVMFunctionEvent:
    name: str
    relative_position: str


@dataclass
class LLVMRewriteTrace:
    initial_config: Pattern
    trace: tuple[LLVMRewriteStep, ...]
    function_events: tuple[LLVMFunctionEvent, ...]

    @staticmethod
    def parse(input: bytes) -> LLVMRewriteTrace:
        parser = LLVMRewriteTraceParser(input)
        ret = parser.read_rewrite_trace()
        assert parser.eof()
        return ret


class LLVMRewriteTraceParser:
    """
    term_with_sentinel := serialized_term 0xcccccccccccccccc
    guarded_term := 0xffffffffffffffff term_with_sentinel
    variable := null_terminated_name term_with_sentinel
    ordinal := uint64
    arity := uint64
    rewrite_trace := ordinal arity variable* guarded_term
    initial_config := guarded_term
    proof_trace := initial_config rewrite_trace*
    """

    end_sentinel: Final = bytes([0xCC] * 8)
    function_event_sentinel: Final = bytes([0xDD] * 8)
    kore_sentinel: Final = bytes([0xFF] * 8)

    def __init__(self, input: bytes):
        self.input = input

    def read_rewrite_trace(self) -> LLVMRewriteTrace:
        events, init_config = self.read_initial_config()
        traces: tuple[LLVMRewriteStep, ...] = ()

        while self.input:
            maybe_event = self.try_read_function_event()
            if maybe_event is not None:
                events = events + (maybe_event,)
            else:
                traces = traces + (self.read_rewrite_step(),)

        return LLVMRewriteTrace(init_config, traces, events)

    def read_initial_config(self) -> tuple[tuple[LLVMFunctionEvent, ...], Pattern]:
        events: tuple[LLVMFunctionEvent, ...] = ()

        while self.input:
            maybe_event = self.try_read_function_event()
            if maybe_event is not None:
                events = events + (maybe_event,)
            else:
                break

        return (events, self.read_guarded_term())

    def read_guarded_term(self) -> Pattern:
        self.read_constant(self.kore_sentinel)
        return self.read_term_with_sentinel()

    def read_term_with_sentinel(self) -> Pattern:
        raw_term = self.read_until(self.end_sentinel)
        self.read_constant(self.end_sentinel)
        llvm_pattern = kllvm_kore.Pattern.deserialize(raw_term)
        assert llvm_pattern, ('Could not deserialize binary kore.', input)
        return llvm_to_kore(llvm_pattern)

    def try_read_function_event(self) -> LLVMFunctionEvent | None:
        if self.try_read_constant(self.function_event_sentinel):
            name = self.read_c_string()
            position = self.read_c_string()
            return LLVMFunctionEvent(name, position)

        return None

    def read_rewrite_step(self) -> LLVMRewriteStep:
        ordinal = self.read_uint64()
        arity = self.read_uint64()

        substitution: tuple[tuple[str, Pattern], ...] = ()
        for _ in range(arity):
            variable_name = self.read_variable_name()
            target = self.read_term_with_sentinel()
            substitution = substitution + ((variable_name, target),)

        term = self.read_guarded_term()
        return LLVMRewriteStep(ordinal, substitution, term)

    def read_variable_name(self) -> str:
        return self.read_c_string()

    def read_c_string(self) -> str:
        ret = str(self.read_until(b'\x00'), 'ascii')
        self.read_constant(b'\x00')
        return ret

    def try_read_constant(self, constant: bytes) -> bool:
        if self.input[: len(constant)] == constant:
            self.input = self.input[len(constant) :]
            return True

        return False

    def read_constant(self, constant: bytes) -> None:
        success = self.try_read_constant(constant)
        assert success

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

    def eof(self) -> bool:
        return len(self.input) == 0
