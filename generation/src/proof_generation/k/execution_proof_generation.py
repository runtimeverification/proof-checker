from __future__ import annotations

from typing import TYPE_CHECKING

import proof_generation.proof as proof
import proof_generation.proofs.kore as kl
import proof_generation.proofs.substitution as subst
from proof_generation.k.kore_convertion.language_semantics import KRewritingRule
from proof_generation.pattern import Symbol

if TYPE_CHECKING:
    from collections.abc import Iterator

    from proof_generation.k.kore_convertion.language_semantics import LanguageSemantics
    from proof_generation.k.kore_convertion.rewrite_steps import RewriteStepExpression
    from proof_generation.pattern import Pattern


class ExecutionProofExp(subst.Substitution):
    def __init__(self, language_semantics: LanguageSemantics, init_config: Pattern):
        self._init_config = init_config
        self._curr_config = init_config
        self.language_semantics = language_semantics
        super().__init__(notations=list(language_semantics.notations) + list(kl.KORE_NOTATIONS))

    @property
    def initial_configuration(self) -> Pattern:
        """Returns the initial configuration."""
        return self._init_config

    @property
    def current_configuration(self) -> Pattern:
        """Returns the current configuration."""
        return self._curr_config

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

    def rewrite_event(self, rule: KRewritingRule, substitution: dict[int, Pattern]) -> proof.ProofThunk:
        """Extends the proof with an additional rewrite step."""
        # Check that the rule is krewrites
        sort, lhs, rhs = sort, _, _ = kl.kore_rewrites.assert_matches(rule.pattern)

        # Check that the lhs matches the current configuration
        # TODO: Move it to the part after the substitution
        # assert (
        #     lhs == self.current_configuration
        # ), f'The current configuration {lhs.pretty(self.pretty_options())} does not match the lhs of the rule {rule.pattern.pretty(self.pretty_options())}'

        # Add the axioms
        self.add_axiom(rule.pattern)

        # Compute the proof
        step_pf = self.load_axiom(rule.pattern)
        subst = substitution
        for name in subst:
            self.assert_functional_pattern(self.language_semantics, subst[name])
            functional_pat = kl.functional(subst[name])
            self.add_assumption(functional_pat)
            functional_assumption = self.load_axiom(functional_pat)
            universalized = self.univ_gene(name, step_pf)
            step_pf = self.functional_subst(universalized, functional_assumption)

        # Add claim
        claim = step_pf.conc
        self.add_claim(claim)
        # TODO: Move here the assertion

        # Add the proof
        self.add_proof_expression(step_pf)
        self._curr_config = rhs
        return step_pf

    def finalize(self) -> None:
        """Prepare proof expression for the final reachability claim"""
        # TODO: Prove the final reachability claim
        return

    @staticmethod
    def from_proof_hints(
        hints: Iterator[RewriteStepExpression], language_semantics: LanguageSemantics
    ) -> proof.ProofExp | ExecutionProofExp:
        """Constructs a proof expression from a list of rewrite hints."""
        proof_expr: ExecutionProofExp | None = None
        for hint in hints:
            if proof_expr is None:
                proof_expr = ExecutionProofExp(language_semantics, hint.configuration_before)

            if isinstance(hint.axiom, KRewritingRule):
                proof_expr.rewrite_event(hint.axiom, hint.substitutions)
            else:
                # TODO: Remove the stub
                raise NotImplementedError('TODO: Add support for equational rules')

        if proof_expr is None:
            print('WARNING: The proof expression is empty, ho hints were provided.')
            return proof.ProofExp(notations=list(language_semantics.notations))
        else:
            return proof_expr
