from __future__ import annotations

from collections.abc import Callable
from typing import TYPE_CHECKING

import proof_generation.proof as proof
import proof_generation.proofs.kore as kl
from proof_generation.k.kore_convertion.language_semantics import KRewritingRule
from proof_generation.pattern import Symbol

if TYPE_CHECKING:
    from collections.abc import Iterator

    from proof_generation.k.kore_convertion.language_semantics import LanguageSemantics
    from proof_generation.k.kore_convertion.rewrite_steps import RewriteStepExpression
    from proof_generation.pattern import Notation, Pattern

ProofMethod = Callable[[proof.ProofExp], proof.ProofThunk]


class ExecutionProofExp(proof.ProofExp):
    def __init__(self, notations: list[Notation]) -> None:
        super().__init__(notations=notations)

    # TODO: Implement the 2 proof rules/lemmas below

    def univ_gene(self, name: int, p: proof.ProofThunk) -> proof.ProofThunk:
        """
               phi
        ------------------
          forall x . phi
        """
        raise NotImplementedError

    # The axiom version of this should also be provable for concrete patterns
    # but we don't worry about this for now
    def functional_subst(self, univ_pf: proof.ProofThunk, func_pf: proof.ProofThunk) -> proof.ProofThunk:
        """
          forall x . phi       functional(rho)
        ----------------------------------------
                    phi[rho / x]
        """
        raise NotImplementedError

    @staticmethod
    def assert_functional_pattern(semantics: LanguageSemantics, pattern: Pattern) -> None:
        sym, _ = kl.deconstruct_nary_application(pattern)
        # TODO: Should we also check that the arguments are functional?
        assert isinstance(sym, Symbol), f'Pattern {pattern} is not supported'
        k_sym = semantics.resolve_to_ksymbol(sym)
        assert k_sym is not None
        assert k_sym.is_functional

    def prove_rewrite_step(self, hint: RewriteStepExpression, language_semantics: LanguageSemantics) -> None:
        """Take a single rewrite step and emit a proof for it."""
        assert isinstance(hint.axiom, KRewritingRule)
        rewrite_axiom = hint.axiom.pattern
        self.add_axiom(rewrite_axiom)
        sort, _, _ = kl.kore_rewrites.assert_matches(rewrite_axiom)
        claim = kl.kore_rewrites(sort, hint.configuration_before, hint.configuration_after)
        self.add_claim(claim)

        step_pf = self.load_axiom(rewrite_axiom)
        subst = hint.substitutions
        for name in subst:
            self.assert_functional_pattern(language_semantics, subst[name])
            functional_pat = kl.functional(subst[name])
            self.add_assumption(functional_pat)
            functional_assumption = self.load_axiom(functional_pat)
            universalized = self.univ_gene(name, step_pf)
            step_pf = self.functional_subst(universalized, functional_assumption)


def generate_proofs(hints: Iterator[RewriteStepExpression], language_semantics: LanguageSemantics) -> ExecutionProofExp:
    proof_expression = ExecutionProofExp(list(language_semantics.notations))
    claims = 0
    for hint in hints:
        proof_expression.prove_rewrite_step(hint, language_semantics)
        claims += 1

    print(f'Generated {claims} claims')
    return proof_expression
