from __future__ import annotations

import sys
from typing import TYPE_CHECKING, BinaryIO

from proof_generation.proof import MetaVar, implies, modus_ponens, prop1, prop2

if TYPE_CHECKING:
    from proof_generation.proof import Pattern, Proof, Term


class Propositional:
    def theory(self) -> list[Pattern]:
        """Returns a list of axioms. In this case we do not rely on any axioms."""
        return []

    def lemmas(self) -> set[Pattern]:
        """Returns a list statements for lemmas that we should reuse."""
        return set()

    def notation(self) -> set[Pattern]:
        """Returns a list patterns that we will want to reuse."""
        return {self.phi0, self.phi0_implies_phi0}

    def claims(self) -> list[Pattern]:
        """Returns a list statements for theorems that we want to publish."""
        return [self.phi0_implies_phi0]

    def proofs(self) -> list[Proof]:
        """Returns a list of proofs for the claims."""
        return [self.imp_reflexivity()]

    def serialize(self, claims_out: BinaryIO, proofs_out: BinaryIO) -> None:
        claims_memory: list[Term] = []
        for claim in self.claims():
            claim.serialize(set(self.notation()), claims_memory, [], claims_out)

        claims: list[Pattern] = self.claims()
        to_reuse: set[Term] = self.notation().union(self.lemmas())
        proofs_memory: list[Term] = []
        for proof in self.proofs():
            proof.serialize(to_reuse, proofs_memory, claims, proofs_out)
        assert claims == []

    phi0: MetaVar = MetaVar(0)
    phi0_implies_phi0: Pattern = implies(phi0, phi0)

    def imp_reflexivity(self) -> Proof:
        return modus_ponens(
            prop1.instantiate(1, self.phi0),
            modus_ponens(
                prop1.instantiate(1, self.phi0_implies_phi0),
                prop2.instantiate(1, self.phi0_implies_phi0).instantiate(2, self.phi0),
            ),
        )


if __name__ == '__main__':
    _exe, claim_path, proof_path = sys.argv
    with open(claim_path, 'wb') as claim_out:
        with open(proof_path, 'wb') as proof_out:
            Propositional().serialize(claim_out, proof_out)
