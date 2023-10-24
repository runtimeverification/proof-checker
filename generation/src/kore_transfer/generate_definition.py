from __future__ import annotations

from collections.abc import Callable
from typing import TYPE_CHECKING

import proof_generation.proof as proof

if TYPE_CHECKING:
    from kore_transfer.generate_hints import KoreHint
    from kore_transfer.kore_converter import Axioms, KoreConverter
    from proof_generation.pattern import Pattern

ProofMethod = Callable[[proof.ProofExp], proof.Proved]


class KoreDefinition(proof.ProofExp):
    axiom_patterns: list[Pattern] = []
    claim_patterns: list[Pattern] = []
    proofs: list[ProofMethod] = []

    @classmethod
    def axioms(cls) -> list[Pattern]:
        return list(cls.axiom_patterns)

    @classmethod
    def claims(cls) -> list[Pattern]:
        return cls.claim_patterns

    @classmethod
    def prove_rewrite_step(cls, claim: Pattern, axiom: Pattern, instantiations: dict[int, Pattern]) -> None:
        """Take a single rewrite step and emit a proof for it."""
        assert len(cls.axiom_patterns) > 0, 'No axioms to prove the rewrite step'
        cls.claim_patterns.append(claim)

        def proof_transition(proof_expr: proof.ProofExp) -> proof.Proved:
            """Prove the transition between two configurations."""
            for pattern in instantiations.values():
                proof_expr.interpreter.pattern(pattern)
            # The axiom pattern must be a rewrite rule
            return proof_expr.interpreter.instantiate(proof_expr.load_axiom(axiom), instantiations)

        cls.proofs.append(proof_transition)

    @classmethod
    def add_axioms(cls, hint: KoreHint, converter: KoreConverter) -> Axioms:
        """Add an axiom to the definition."""
        axioms = converter.collect_functional_axioms(hint)
        axioms.setdefault(hint.axiom.kind, []).append(hint.axiom)
        cls.axiom_patterns.append(hint.axiom.pattern)
        return axioms

    def proof_expressions(self) -> list[proof.ProvedExpression]:
        def make_function(obj: KoreDefinition, func: ProofMethod) -> proof.ProvedExpression:
            return lambda: func(obj)

        return [make_function(self, proof_func) for proof_func in self.proofs]
