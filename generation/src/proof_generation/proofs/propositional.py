from __future__ import annotations

import sys
from typing import TYPE_CHECKING, BinaryIO

from proof_generation.proof import Implication, MetaVar, ModusPonens, Mu, Prop1, Prop2, SVar, implies

if TYPE_CHECKING:
    from proof_generation.proof import Pattern, Proof, Term


class ProofExp:
    def prop1(self) -> Proof:
        return Prop1()

    def prop2(self) -> Proof:
        return Prop2()

    def modus_ponens(self, left: Proof, right: Proof) -> Proof:
        return ModusPonens(left, right)


class Propositional(ProofExp):
    def theory(self) -> list[Pattern]:
        """Returns a list of axioms. In this case we do not rely on any axioms."""
        return []

    def lemmas(self) -> set[Pattern]:
        """Returns a list statements for lemmas that we should reuse."""
        return set()

    def notation(self) -> set[Pattern]:
        """Returns a list patterns that we will want to reuse."""
        return {self.phi0, self.bot(), self.top(), self.phi0_implies_phi0}

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

    def bot(self) -> Pattern:
        return Mu(SVar(0), SVar(0))

    def neg(self, p: Pattern) -> Pattern:
        return implies(p, self.bot())

    def top(self) -> Pattern:
        return self.neg(self.bot())

    def imp_reflexivity(self) -> Proof:
        return self.modus_ponens(
            self.prop1().instantiate(1, self.phi0),
            self.modus_ponens(
                self.prop1().instantiate(1, self.phi0_implies_phi0),
                self.prop2().instantiate(1, self.phi0_implies_phi0).instantiate(2, self.phi0),
            ),
        )

    def imp_transitivity(self, left: Proof, right: Proof) -> Proof:
        left_conc = left.conclusion()
        match left_conc:
            case Implication(phi0, phi1):
                pass
            case _:
                raise AssertionError('Expected implication')
        right_conc = right.conclusion()
        match right_conc:
            case Implication(phi1_r, phi2):
                assert phi1_r == phi1
            case _:
                raise AssertionError('Expected implication')

        step1 = self.modus_ponens(right, self.prop1().instantiate(0, right_conc))
        step2 = self.modus_ponens(
            step1,
            self.prop2().instantiate(1, phi1).instantiate(2, phi2).instantiate(0, MetaVar(1)),
        )
        return self.modus_ponens(left, step2.instantiate(1, phi0))


if __name__ == '__main__':
    _exe, claim_path, proof_path = sys.argv
    with open(claim_path, 'wb') as claim_out:
        with open(proof_path, 'wb') as proof_out:
            Propositional().serialize(claim_out, proof_out)
