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
    prove_step_axioms: list[Pattern] = []
    whitelist_axioms: list[Pattern] = []
    prove_step_claims: list[Pattern] = []
    proofs: list[ProofMethod] = []

    @classmethod
    def axioms(cls) -> list[Pattern]:
        return list(cls.prove_step_axioms)

    @classmethod
    def claims(cls) -> list[Pattern]:
        return cls.prove_step_claims

    @classmethod
    def prove_rewrite_step(cls, claim: Pattern, axiom: Pattern, instantiations: dict[int, Pattern]) -> None:
        """Take a single rewrite step and emit a proof for it."""
        assert len(cls.prove_step_axioms) > 0, 'No axioms to prove the rewrite step'
        cls.prove_step_claims.append(claim)

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
        cls.prove_step_axioms.append(hint.axiom.pattern)
        return axioms

    @classmethod
    def add_whitelist_axioms(cls, hint: KoreHint, converter: KoreConverter) -> Axioms:
        """Add a hook call as a whitelist axiom to the definition."""
        axioms = converter.construct_event_axioms(hint)
        cls.whitelist_axioms.extend([a.pattern for alist in axioms.values() for a in alist])
        return axioms

    def proof_expressions(self) -> list[proof.ProvedExpression]:
        def make_function(obj: KoreDefinition, func: ProofMethod) -> proof.ProvedExpression:
            return lambda: func(obj)

        return [make_function(self, proof_func) for proof_func in self.proofs]
