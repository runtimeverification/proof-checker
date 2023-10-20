from __future__ import annotations

from collections.abc import Callable
from typing import TYPE_CHECKING

import proof_generation.proof as proof

if TYPE_CHECKING:
    import proof_generation.pattern as nf
    from kore_transfer.kore_converter import KoreConverter

ProofMethod = Callable[[proof.ProofExp], proof.Proved]


class KoreDefinition(proof.ProofExp):
    axiom_patterns: dict[int, nf.Pattern] = {}
    claim_patterns: list[nf.Pattern] = []
    proofs: list[ProofMethod] = []

    @classmethod
    def axioms(cls) -> list[nf.Pattern]:
        return list(cls.axiom_patterns.values())

    @classmethod
    def claims(cls) -> list[nf.Pattern]:
        return cls.claim_patterns

    @classmethod
    def prove_rewrite_step(cls, claim: nf.Pattern, axiom: nf.Pattern, instantiations: dict[int, nf.Pattern]) -> None:
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
    def add_axiom(cls, position: int, converter: KoreConverter) -> nf.Pattern:
        """Add an axiom to the definition."""
        new_axiom = converter.retrieve_axiom(position)
        cls.axiom_patterns[position] = new_axiom
        return new_axiom

    def proof_expressions(self) -> list[proof.ProvedExpression]:
        def make_function(obj: KoreDefinition, func: ProofMethod) -> proof.ProvedExpression:
            return lambda: func(obj)

        return [make_function(self, proof_func) for proof_func in self.proofs]
