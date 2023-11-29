from __future__ import annotations

from typing import TYPE_CHECKING

import proof_generation.proof as proof
import proof_generation.proofs.kore as kl
from proof_generation.k.kore_convertion.language_semantics import AxiomType, ConvertedAxiom, KRewritingRule
from proof_generation.pattern import Symbol
from proof_generation.proofs.definedness import functional
from proof_generation.proofs.substitution import Substitution

if TYPE_CHECKING:
    from collections.abc import Iterator

    from proof_generation.k.kore_convertion.language_semantics import LanguageSemantics
    from proof_generation.k.kore_convertion.rewrite_steps import RewriteStepExpression
    from proof_generation.pattern import Pattern


class ExecutionProofExp(proof.ProofExp):
    def __init__(self, language_semantics: LanguageSemantics, init_config: Pattern):
        self._init_config = init_config
        self._curr_config = init_config
        self.language_semantics = language_semantics
        super().__init__(notations=list(language_semantics.notations))
        self.subst_proofexp = self.add_submodule(Substitution())
        self.kore_lemmas = self.add_submodule(kl.KoreLemmas())

    @property
    def initial_configuration(self) -> Pattern:
        """Returns the initial configuration."""
        return self._init_config

    @staticmethod
    def collect_functional_axioms(
        language_semantics: LanguageSemantics, substitutions: dict[int, Pattern]
    ) -> list[ConvertedAxiom]:
        subst_axioms = []
        for pattern in substitutions.values():
            # Doublecheck that the pattern is a functional symbol and it is valid to generate the axiom
            sym, _ = kl.deconstruct_nary_application(pattern)
            assert isinstance(sym, Symbol), f'Pattern {pattern} is not supported'
            k_sym = language_semantics.resolve_to_ksymbol(sym)
            assert k_sym is not None
            assert k_sym.is_functional
            converted_pattern = functional(pattern)
            subst_axioms.append(ConvertedAxiom(AxiomType.FunctionalSymbol, converted_pattern))
        return subst_axioms

    def add_assumptions_for_rewrite_step(self, rule: KRewritingRule, substitutions: dict[int, Pattern]) -> None:
        """Add axioms to the definition."""
        # TODO: We don't use them until the substitutions are implemented
        func_axioms = ExecutionProofExp.collect_functional_axioms(self.language_semantics, substitutions)
        self.add_assumptions([axiom.pattern for axiom in func_axioms])
        self.add_axiom(rule.pattern)

    @property
    def current_configuration(self) -> Pattern:
        """Returns the current configuration."""
        return self._curr_config

    def rewrite_event(self, rule: KRewritingRule, substitution: dict[int, Pattern]) -> proof.ProofThunk:
        """Extends the proof with an additional rewrite step."""
        # Check that the rule is krewrites
        instantiated_axiom = rule.pattern.instantiate(substitution)
        match = kl.kore_rewrites.assert_matches(instantiated_axiom)
        lhs = match[1]
        rhs = match[2]

        # Check that the lhs matches the current configuration
        assert (
            lhs == self.current_configuration
        ), f'The current configuration {lhs.pretty(self.pretty_options())} does not match the lhs of the rule {rule.pattern.pretty(self.pretty_options())}'

        # Add the axioms
        self.add_assumptions_for_rewrite_step(rule, substitution)

        # Add the claim
        self.add_claim(instantiated_axiom)

        # Add the proof
        proof = self.dynamic_inst(self.load_axiom(rule.pattern), substitution)
        self.add_proof_expression(proof)
        self._curr_config = rhs
        return proof

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
