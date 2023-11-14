from __future__ import annotations

import struct
from dataclasses import dataclass
from typing import TYPE_CHECKING

from pyk.kllvm import ast as kllvm_kore
from pyk.kllvm.convert import llvm_to_kore

if TYPE_CHECKING:
    import pyk.kore.syntax as kore


@dataclass
class LLVMRewriteStep:
    rule_ordinal: int
    substitution: tuple[tuple[str, kore.Pattern], ...]
    post_config: kore.Pattern


@dataclass
class LLVMRewriteTrace:
    initial_config: kore.Pattern
    trace: tuple[LLVMRewriteStep, ...]

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

    def __init__(self, input: bytes):
        self.input = input

    def read_rewrite_trace(self) -> LLVMRewriteTrace:
        init_config = self.read_guarded_term()
        traces: tuple[LLVMRewriteStep, ...] = ()
        while self.input:
            traces = traces + (self.read_rewrite_step(),)
        return LLVMRewriteTrace(init_config, traces)

    def read_guarded_term(self) -> kore.Pattern:
        self.read_constant(bytes([0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF]))
        return self.read_term_with_sentinel()

    def read_term_with_sentinel(self) -> kore.Pattern:
        sentinal = bytes(
            [
                0xCC,
                0xCC,
                0xCC,
                0xCC,
                0xCC,
                0xCC,
                0xCC,
                0xCC,
            ]
        )
        raw_term = self.read_until(sentinal)
        self.read_constant(sentinal)
        llvm_pattern = kllvm_kore.Pattern.deserialize(raw_term)
        assert llvm_pattern, ('Could not deserialize binary kore.', input)
        return llvm_to_kore(llvm_pattern)

    def read_rewrite_step(self) -> LLVMRewriteStep:
        ordinal = self.read_uint64()
        arity = self.read_uint64()

        substitution: tuple[tuple[str, kore.Pattern], ...] = ()
        for _ in range(arity):
            variable_name = self.read_variable_name()
            target = self.read_term_with_sentinel()
            substitution = substitution + ((variable_name, target),)

        term = self.read_guarded_term()
        return LLVMRewriteStep(ordinal, substitution, term)

    def read_variable_name(self) -> str:
        ret = str(self.read_until(b'\x00'), 'ascii')
        self.read_constant(b'\x00')
        return ret

    def read_constant(self, constant: bytes) -> None:
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

    def eof(self) -> bool:
        return len(self.input) == 0
