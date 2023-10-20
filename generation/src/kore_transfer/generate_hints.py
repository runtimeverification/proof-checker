from __future__ import annotations

from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from collections.abc import Iterator

    import pyk.kore.syntax as kore

    import proof_generation.pattern as nf
    from kore_transfer.kore_converter import KoreConverter
    from rewrite.llvm_proof_hint import LLVMRewriteTrace


class KoreHint:
    def __init__(self, pattern: nf.Pattern, axiom_ordinal: int, instantiations: dict[int, nf.Pattern]) -> None:
        # TODO: Change interface according to the real hint format
        self._pattern: nf.Pattern = pattern
        self._axiom_ordinal: int = axiom_ordinal
        self._instantiations: dict[int, nf.Pattern] = instantiations

    @property
    def pattern(self) -> nf.Pattern:
        return self._pattern

    @property
    def axiom_ordinal(self) -> int:
        """Return the relevant axiom for the given hint."""
        return self._axiom_ordinal

    @property
    def instantiations(self) -> dict[int, nf.Pattern]:
        return self._instantiations


def get_proof_hints(
    llvm_proof_hint: LLVMRewriteTrace,
    axioms: list[kore.Axiom],
    kore_converter: KoreConverter,
) -> Iterator[KoreHint]:
    """Emits proof hints corresponding to the given LLVM rewrite trace."""
    pre_config = kore_converter.convert_pattern(llvm_proof_hint.initial_config)

    # Note that no hints will be generated if the trace is empty
    post_config = pre_config
    for rewrite_step in llvm_proof_hint.trace:
        pre_config = post_config
        subst = kore_converter.convert_substitution(rewrite_step.substitution)
        hint = KoreHint(pre_config, rewrite_step.rule_ordinal, subst)
        post_config = kore_converter.convert_pattern(rewrite_step.post_config)
        yield hint
