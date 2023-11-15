from __future__ import annotations

from abc import ABC
from dataclasses import dataclass
from typing import TYPE_CHECKING

import pyk.kore.syntax as pk

from proof_generation.llvm_proof_hint import LLVMRuleEvent

if TYPE_CHECKING:
    from collections.abc import Iterator

    from kore_transfer.kore_convertion.language_semantics import KEquationalRule, KRewritingRule, LanguageSemantics
    from proof_generation.llvm_proof_hint import LLVMRewriteTrace
    from proof_generation.pattern import Pattern


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
        conf_before: Pattern,
        conf_after: Pattern,
        axiom: KRewritingRule | KEquationalRule,
        substitutions: dict[int, Pattern],
    ) -> None:
        # TODO: Change interface according to the real hint format
        self._pre_configuration: Pattern = conf_before
        self._post_configuration: Pattern = conf_after
        self._axiom: KRewritingRule | KEquationalRule = axiom
        self._substitutions: dict[int, Pattern] = substitutions

    @property
    def configuration_before(self) -> Pattern:
        return self._pre_configuration

    @property
    def configuration_after(self) -> Pattern:
        return self._post_configuration

    @property
    def axiom(self) -> KRewritingRule | KEquationalRule:
        return self._axiom

    @property
    def substitutions(self) -> dict[int, Pattern]:
        return self._substitutions


def get_proof_hints(
    llvm_proof_hint: LLVMRewriteTrace,
    language_semantics: LanguageSemantics,
) -> Iterator[RewriteStepExpression]:
    """
    Emits proof hints corresponding to the given LLVM rewrite trace.
    Note that no hints will be generated if the trace is empty.
    """

    # TODO: process function/hook/rule events in llvm_proof_hint.pre_trace
    pre_config = language_semantics.convert_pattern(llvm_proof_hint.initial_config)

    post_config = pre_config
    if len(llvm_proof_hint.trace) > 0:
        for e1, e2 in zip(llvm_proof_hint.trace, llvm_proof_hint.trace[1:], strict=False):
            # TODO: process function/hook events in llvm_proof_hint.strace
            if isinstance(e1, LLVMRuleEvent) and isinstance(e2, pk.Pattern):
                # generate the hint using the new format
                pre_config = post_config
                post_config = language_semantics.convert_pattern(e2)

                axiom = language_semantics.get_axiom(e1.rule_ordinal)
                substitutions = language_semantics.convert_substitutions(dict(e1.substitution), e1.rule_ordinal)

                hint = RewriteStepExpression(pre_config, post_config, axiom, substitutions)
                yield hint
