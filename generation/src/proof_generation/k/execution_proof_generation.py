from __future__ import annotations

from typing import TYPE_CHECKING

import proof_generation.proof as proof
import proof_generation.proofs.kore as kl
from proof_generation.k.kore_convertion.language_semantics import KRewritingRule
from proof_generation.pattern import EVar, Symbol
from proof_generation.proofs.definedness import functional
from proof_generation.proofs.substitution import Substitution

if TYPE_CHECKING:
    from collections.abc import Iterator

    from proof_generation.k.kore_convertion.language_semantics import LanguageSemantics
    from proof_generation.k.kore_convertion.rewrite_steps import RewriteStepExpression
    from proof_generation.pattern import Pattern


class ExecutionProofExp(proof.ProofExp):
    def __init__(self, language_semantics: LanguageSemantics, init_config: Pattern):
        self.subst_proofexp = Substitution()
        self.kore_lemmas = kl.KoreLemmas()
        self._init_config = init_config
        self._curr_config = init_config
        self.language_semantics = language_semantics
        super().__init__(notations=list(language_semantics.notations))
        self.add_notations(self.subst_proofexp.get_notations())
        self.add_notations(self.kore_lemmas.get_notations())

    @property
    def initial_configuration(self) -> Pattern:
        """Returns the initial configuration."""
        return self._init_config

    @property
    def current_configuration(self) -> Pattern:
        """Returns the current configuration."""
        return self._curr_config

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

        # Add the axioms
        self.add_axiom(rule.pattern)

        # Compute the proof
        step_pf = self.load_axiom(rule.pattern)
        for name, plug in substitution.items():
            self.assert_functional_pattern(self.language_semantics, plug)
            functional_pat = functional(plug)
            self.add_assumption(functional_pat)
            functional_assumption = self.load_axiom(functional_pat)
            universalized = self.subst_proofexp.universal_gen(step_pf, EVar(name))
            step_pf = self.subst_proofexp.functional_subst(functional_assumption, universalized)

        # Add claim
        claim = rule.pattern
        for name, plug in substitution.items():
            claim = claim.apply_esubst(name, plug)
        self.add_claim(claim)

        assert (
            lhs == self.current_configuration
        ), f'The current configuration {lhs.pretty(self.pretty_options())} does not match the lhs of the rule {rule.pattern.pretty(self.pretty_options())}'

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
    ) -> proof.ProofExp:
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
