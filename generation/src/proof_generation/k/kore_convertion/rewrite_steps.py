from __future__ import annotations

from abc import ABC
from collections.abc import Iterator
from dataclasses import dataclass
from typing import TYPE_CHECKING

from frozendict import frozendict

from proof_generation.llvm_proof_hint import LLVMFunctionEvent, LLVMRuleEvent

if TYPE_CHECKING:
    from proof_generation.aml import Pattern
    from proof_generation.k.kore_convertion.language_semantics import KEquationalRule, KRewritingRule, LanguageSemantics
    from proof_generation.llvm_proof_hint import LLVMRewriteTrace


# An abstract super class for user-defined and hook function events
@dataclass
class HintEvent(ABC):
    name: str


# Events for user-defined functions
@dataclass
class FunEvent(HintEvent):
    position: tuple[int, ...]


# Events for built-in functions
@dataclass
class HookEvent(HintEvent):
    args: tuple[Pattern | HintEvent, ...]
    result: Pattern


@dataclass
class RewriteStepExpression:
    axiom: KRewritingRule | KEquationalRule
    substitutions: frozendict[int, Pattern]


EventTrace = Iterator[FunEvent | RewriteStepExpression]


def get_proof_hints(
    rewrite_trace: LLVMRewriteTrace,
    language_semantics: LanguageSemantics,
) -> tuple[Pattern, EventTrace]:
    """
    Emits proof hints corresponding to the given LLVM rewrite trace.
    Note that no hints will be generated if the trace is empty.
    """

    # TODO: process function/hook/rule events in llvm_proof_hint.pre_trace
    current_config = language_semantics.convert_pattern(rewrite_trace.initial_config)
    iterator = _iterate_over_hints(rewrite_trace, language_semantics)
    return current_config, iterator


def _iterate_over_hints(
    rewrite_trace: LLVMRewriteTrace,
    language_semantics: LanguageSemantics,
) -> EventTrace:
    """
    Emits proof hints corresponding to the given LLVM rewrite trace.
    Note that no hints will be generated if the trace is empty.
    """
    # TODO: process function/hook/rule events in llvm_proof_hint.pre_trace
    non_empty = False
    for event in rewrite_trace.trace:
        # TODO: process function/hook events in llvm_proof_hint.strace
        match event:
            case LLVMRuleEvent(rule_ordinal, substitutions):
                axiom = language_semantics.get_axiom(rule_ordinal)
                converted_substitutions = language_semantics.convert_substitutions(dict(substitutions), rule_ordinal)
                non_empty = True
                yield RewriteStepExpression(axiom, frozendict(converted_substitutions))
            case LLVMFunctionEvent(name, location_str, _):
                location: tuple[int, ...] = tuple(map(int, location_str.split(':')))
                non_empty = True
                yield FunEvent(name, location)
            case _:
                continue
    else:
        assert non_empty, 'The hints trace is empty.'
