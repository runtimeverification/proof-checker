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
    max_step: int,
) -> Iterator[KoreHint]:
    """Emits proof hints corresponding to the given LLVM rewrite trace."""
    assert max_step <= len(
        llvm_proof_hint.trace
    ), f'The requested number of rewrites {max_step} exceeds the length of the given trace {len(llvm_proof_hint.trace)}!'

    pre_config = kore_converter.convert_pattern(llvm_proof_hint.initial_config)

    # TODO: Handle the no-rewrites case, which requires changing the KoreHints representation
    if max_step <= 0:
        pass
        # yield KoreHint(pre_config, None, None)
    else:
        # Note that here len(llvm_proof_hint.trace) > 0
        post_config = pre_config
        for step in range(max_step):
            rewrite_step = llvm_proof_hint.trace[step]
            pre_config = post_config
            axiom = kore_converter.convert_axiom(axioms[rewrite_step.rule_ordinal])
            subst = kore_converter.convert_substitution(rewrite_step.substitution)
            hint = KoreHint(pre_config, axiom, subst)
            post_config = kore_converter.convert_pattern(rewrite_step.post_config)
            yield hint
