from __future__ import annotations

from abc import ABC
from dataclasses import dataclass
from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from collections.abc import Iterator

    from kore_transfer.kore_converter import ConvertedAxiom, KoreConverter
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


class KoreHint:
    def __init__(
        self,
        conf_before: Pattern,
        fun_events: tuple[HintEvent, ...],
        conf_after: Pattern,
        axiom: ConvertedAxiom,
        substitutions: dict[int, Pattern],
    ) -> None:
        # TODO: Change interface according to the real hint format
        self._pre_configuration: Pattern = conf_before
        self._fun_events: tuple[HintEvent, ...] = fun_events
        self._post_configuration: Pattern = conf_after
        self._axiom: ConvertedAxiom = axiom
        self._substitutions: dict[int, Pattern] = substitutions

    @property
    def configuration_before(self) -> Pattern:
        return self._pre_configuration

    @property
    def functional_events(self) -> tuple[HintEvent, ...]:
        return self._fun_events

    @property
    def configuration_after(self) -> Pattern:
        return self._post_configuration

    @property
    def axiom(self) -> ConvertedAxiom:
        return self._axiom

    @property
    def substitutions(self) -> dict[int, Pattern]:
        return self._substitutions


def get_proof_hints(
    llvm_proof_hint: LLVMRewriteTrace,
    kore_converter: KoreConverter,
) -> Iterator[KoreHint]:
    """Emits proof hints corresponding to the given LLVM rewrite trace."""
    pre_config = kore_converter.convert_pattern(llvm_proof_hint.initial_config)

    # Note that no hints will be generated if the trace is empty
    post_config = pre_config
    for rewrite_step in llvm_proof_hint.trace:
        # generate the hint using the new format
        pre_config = post_config
        post_config = kore_converter.convert_pattern(rewrite_step.post_config)

        axiom, substitutions = kore_converter.retrieve_axiom_with_substitutions(rewrite_step.rule_ordinal, dict(rewrite_step.substitution))

        # TODO: read function/hook events from the given trace
        fun_events = ()

        hint = KoreHint(pre_config, fun_events, post_config, axiom, substitutions)
        yield hint
