from __future__ import annotations

from collections.abc import Callable
from typing import TYPE_CHECKING

import pyk.kore.syntax as kore

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
    def prove_rewrite_step(cls, claim: nf.Pattern, ordinal: int, instantiations: dict[int, nf.Pattern]) -> None:
        """Take a single rewrite step and emit a proof for it."""
        assert len(cls.axiom_patterns) > 0, 'No axioms to prove the rewrite step'
        cls.claim_patterns.append(claim)

        def proof_transition(proof_expr: proof.ProofExp) -> proof.Proved:
            """Prove the transition between two configurations."""
            for pattern in instantiations.values():
                proof_expr.interpreter.pattern(pattern)
            # The axiom pattern must be a rewrite rule
            return proof_expr.interpreter.instantiate(
                proof_expr.load_axiom(cls.axiom_patterns[ordinal]), instantiations
            )

        cls.proofs.append(proof_transition)

    def proof_expressions(self) -> list[proof.ProvedExpression]:
        def make_function(obj: KoreDefinition, func: ProofMethod) -> proof.ProvedExpression:
            return lambda: func(obj)

        return [make_function(self, proof_func) for proof_func in self.proofs]


def compose_definition(kore_definition: kore.Definition, converter: KoreConverter) -> type[KoreDefinition]:
    """Compose the proofs for all steps."""
    extracted_axioms = {}
    ordinal = 0
    for module in kore_definition.modules:
        for axiom in module.axioms:
            pattern = axiom.pattern
            # Select only patterns below that starts with kore.Rewrites
            if isinstance(pattern, kore.Rewrites):
                extracted_axioms[ordinal] = _convert_axiom(pattern, converter)
            ordinal += 1

    KoreDefinition.axiom_patterns.update(extracted_axioms)
    return KoreDefinition


def _convert_axiom(pattern: kore.Pattern, converter: KoreConverter) -> nf.Pattern:
    assert isinstance(pattern, kore.Rewrites)
    assert isinstance(pattern.left, kore.And)
    assert isinstance(pattern.right, kore.And)
    # TODO: Remove side conditions for now
    preprocessed_pattern = kore.Rewrites(pattern.sort, pattern.left.left, pattern.right.left)
    return converter.convert_pattern(preprocessed_pattern)
