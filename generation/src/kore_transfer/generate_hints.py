from __future__ import annotations

from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from collections.abc import Iterator

    import pyk.kore.syntax as kore

    import proof_generation.pattern as nf
    from kore_transfer.kore_converter import KoreConverter
    from rewrite.llvm_proof_hint import LLVMRewriteTrace


class KoreHint:
    def __init__(self, pattern: nf.Pattern, axiom: nf.Pattern, instantiations: dict[int, nf.Pattern]) -> None:
        # TODO: Change interface according to the real hint format
        self._pattern: nf.Pattern = pattern
        self._axiom: nf.Pattern = axiom
        self._instantiations: dict[int, nf.Pattern] = instantiations

    @property
    def pattern(self) -> nf.Pattern:
        return self._pattern

    @property
    def relevant_axiom(self) -> nf.Pattern:
        """Return the relevant axiom for the given hint."""
        return self._axiom

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
        print(f'ordinal: {rewrite_step.rule_ordinal}')
        print(f'substitution: {rewrite_step.substitution}')
        axiom = kore_converter.convert_axiom(axioms[rewrite_step.rule_ordinal])
        subst = kore_converter.convert_substitution(rewrite_step.substitution)
        hint = KoreHint(pre_config, axiom, subst)
        post_config = kore_converter.convert_pattern(rewrite_step.post_config)
        yield hint
