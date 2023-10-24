from __future__ import annotations

from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from collections.abc import Iterator

    from kore_transfer.kore_converter import ConvertedAxiom, KoreConverter
    from proof_generation.pattern import Pattern
    from rewrite.llvm_proof_hint import LLVMRewriteTrace


class KoreHint:
    def __init__(
        self, conf_before: Pattern, conf_after: Pattern, axiom: ConvertedAxiom, substitutions: dict[int, Pattern]
    ) -> None:
        # TODO: Change interface according to the real hint format
        self._pre_configuration: Pattern = conf_before
        self._post_configuration: Pattern = conf_after
        self._axiom: ConvertedAxiom = axiom
        self._substitutions: dict[int, Pattern] = substitutions

    @property
    def configuration_before(self) -> Pattern:
        return self._pre_configuration

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

        axiom = kore_converter.retrieve_axiom_for_ordinal(rewrite_step.rule_ordinal)
        substitutions = kore_converter.convert_substitutions(dict(rewrite_step.substitution))

        hint = KoreHint(pre_config, post_config, axiom, substitutions)
        yield hint
