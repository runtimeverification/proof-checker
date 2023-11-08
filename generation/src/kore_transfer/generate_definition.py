from __future__ import annotations

from collections.abc import Callable
from typing import TYPE_CHECKING

import proof_generation.proof as proof
from kore_transfer.kore_converter import KRewritingRule

if TYPE_CHECKING:
    from kore_transfer.generate_hints import KoreHint
    from kore_transfer.kore_converter import LanguageSemantics
    from proof_generation.pattern import Pattern

ProofMethod = Callable[[proof.ProofExp], proof.ProofThunk]


class KoreDefinition(proof.ProofExp):
    prove_step_axioms: list[Pattern] = []
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

        def proof_transition(proof_expr: proof.ProofExp) -> proof.ProofThunk:
            return proof_expr.dynamic_inst(proof_expr.load_axiom(axiom), instantiations)

        cls.proofs.append(proof_transition)

    @classmethod
    def add_axioms(cls, hint: KoreHint, converter: LanguageSemantics) -> KRewritingRule:
        """Add axioms to the definition."""
        # TODO: We don't use them so far
        converter.collect_functional_axioms(hint)
        cls.prove_step_axioms.append(hint.axiom.pattern)
        assert isinstance(hint.axiom, KRewritingRule)
        return hint.axiom

    def proof_expressions(self) -> list[proof.ProofThunk]:
        return [proof_func(self) for proof_func in self.proofs]
