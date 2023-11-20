from __future__ import annotations

from collections.abc import Callable
from typing import TYPE_CHECKING

import proof_generation.proof as proof
import proof_generation.proofs.kore as kl
from proof_generation.k.kore_convertion.language_semantics import AxiomType, ConvertedAxiom, KRewritingRule
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

    @staticmethod
    def collect_functional_axioms(semantics: LanguageSemantics, hint: RewriteStepExpression) -> list[ConvertedAxiom]:
        subst_axioms = []
        for pattern in hint.substitutions.values():
            # Doublecheck that the pattern is a functional symbol and it is valid to generate the axiom
            sym, args = kl.deconstruct_nary_application(pattern)
            assert isinstance(sym, Symbol), f'Pattern {pattern} is not supported'
            assert sym.name.startswith('kore_')
            assert semantics.get_symbol(sym.name.removeprefix('kore_')).is_functional
            converted_pattern = kl.functional(pattern)
            subst_axioms.append(ConvertedAxiom(AxiomType.FunctionalSymbol, converted_pattern))
        return subst_axioms

    def add_assumptions_for_rewrite_step(
        self, hint: RewriteStepExpression, language_semantics: LanguageSemantics
    ) -> KRewritingRule:
        """Add axioms to the definition."""
        # TODO: We don't use them until the substitutions are implemented
        func_axioms = ExecutionProofExp.collect_functional_axioms(language_semantics, hint)
        self.add_assumptions([axiom.pattern for axiom in func_axioms])
        assert isinstance(hint.axiom, KRewritingRule)
        self.add_axiom(hint.axiom.pattern)
        return hint.axiom

    def prove_rewrite_step(self, claim: Pattern, axiom: Pattern, instantiations: dict[int, Pattern]) -> None:
        """Take a single rewrite step and emit a proof for it."""
        assert len(self._axioms) > 0, 'No axioms to prove the rewrite step'
        self._claims.append(claim)
        self._proof_expressions.append(self.dynamic_inst(self.load_axiom(axiom), instantiations))


def generate_proofs(hints: Iterator[RewriteStepExpression], language_semantics: LanguageSemantics) -> ExecutionProofExp:
    proof_expression = ExecutionProofExp(list(language_semantics.notations))
    claims = 0
    for hint in hints:
        axiom = proof_expression.add_assumptions_for_rewrite_step(hint, language_semantics)
        assert isinstance(axiom, KRewritingRule)
        rewrite_axiom = axiom.pattern
        sort, _, _ = kl.kore_rewrites.assert_matches(rewrite_axiom)
        claim = kl.kore_rewrites(sort, hint.configuration_before, hint.configuration_after)

        proof_expression.prove_rewrite_step(claim, rewrite_axiom, hint.substitutions)
        claims += 1

    print(f'Generated {claims} claims')
    return proof_expression
