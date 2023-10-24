from __future__ import annotations

from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from collections.abc import Iterator

    from kore_transfer.kore_converter import KoreConverter
    from proof_generation.pattern import Pattern
    from rewrite.llvm_proof_hint import LLVMRewriteTrace


class KoreHint:
    def __init__(
        self, conf_before: Pattern, conf_after: Pattern, axiom_ordinal: int, substitutions: dict[str, Pattern]
    ) -> None:
        # TODO: Change interface according to the real hint format
        self._pre_configuration: Pattern = conf_before
        self._post_configuration: Pattern = conf_after
        self._axiom_ordinal: int = axiom_ordinal
        self._substitutions: dict[str, Pattern] = substitutions

    @property
    def configuration_before(self) -> Pattern:
        return self._pre_configuration

    @property
    def configuration_after(self) -> Pattern:
        return self._post_configuration

    @property
    def axiom_ordinal(self) -> int:
        return self._axiom_ordinal

    @property
    def substitutions(self) -> dict[str, Pattern]:
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
        substitutions = {
            name: kore_converter.convert_pattern(pattern) for name, pattern in dict(rewrite_step.substitution).items()
        }
        hint = KoreHint(pre_config, post_config, rewrite_step.rule_ordinal, substitutions)
        yield hint
