from __future__ import annotations

from abc import ABC
from dataclasses import dataclass
from typing import TYPE_CHECKING

from proof_generation.llvm_proof_hint import LLVMRuleEvent

if TYPE_CHECKING:
    from collections.abc import Iterator

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


class RewriteStepExpression:
    def __init__(
        self,
        axiom: KRewritingRule | KEquationalRule,
        substitutions: dict[int, Pattern],
    ) -> None:
        self._axiom: KRewritingRule | KEquationalRule = axiom
        self._substitutions: dict[int, Pattern] = substitutions

    @property
    def axiom(self) -> KRewritingRule | KEquationalRule:
        return self._axiom

    @property
    def substitutions(self) -> dict[int, Pattern]:
        return self._substitutions


def get_proof_hints(
    llvm_proof_hints: LLVMRewriteTrace,
    language_semantics: LanguageSemantics,
) -> tuple[Pattern, Iterator[RewriteStepExpression]]:
    """
    Emits proof hints corresponding to the given LLVM rewrite trace.
    Note that no hints will be generated if the trace is empty.
    """

    # TODO: process function/hook/rule events in llvm_proof_hint.pre_trace
    current_config = language_semantics.convert_pattern(llvm_proof_hints.initial_config)
    iterator = _iterate_over_hints(llvm_proof_hints, language_semantics)
    return current_config, iterator


def _iterate_over_hints(
    llvm_proof_hints: LLVMRewriteTrace,
    language_semantics: LanguageSemantics,
) -> Iterator[RewriteStepExpression]:
    """
    Emits proof hints corresponding to the given LLVM rewrite trace.
    Note that no hints will be generated if the trace is empty.
    """
    # TODO: process function/hook/rule events in llvm_proof_hint.pre_trace
    for event in llvm_proof_hints.trace:
        # TODO: process function/hook events in llvm_proof_hint.strace
        if isinstance(event, LLVMRuleEvent):
            axiom = language_semantics.get_axiom(event.rule_ordinal)
            substitutions = language_semantics.convert_substitutions(dict(event.substitution), event.rule_ordinal)
            hint = RewriteStepExpression(axiom, substitutions)
            yield hint
