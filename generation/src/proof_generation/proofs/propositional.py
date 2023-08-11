from __future__ import annotations

import sys
from typing import TYPE_CHECKING, BinaryIO

from proof_generation.instruction import Instruction
from proof_generation.proof import Implication, MetaVar, ModusPonens, Mu, Prop1, Prop2, SVar, implies

if TYPE_CHECKING:
    from proof_generation.proof import Pattern, Proof


class ProofExp:
    def prop1(self) -> Proof:
        return Prop1()

    def prop2(self) -> Proof:
        return Prop2()

    # Flipping wrapper for easier-to-read proofs from MM files
    def modus_ponens(self, left: Proof, right: Proof) -> Proof:
        return ModusPonens(right, left)


class Propositional(ProofExp):
    def theory(self) -> list[Pattern]:
        """Returns a list of axioms. In this case we do not rely on any axioms."""
        return []

    def lemmas(self) -> set[Pattern]:
        """Returns a list statements for internal lemmas that we should reuse."""
        return set(self.claims())

    def notation(self) -> set[Pattern]:
        """Returns a list patterns that we will want to reuse."""
        return {self.phi0, self.bot(), self.top(), self.phi0_implies_phi0}

    def claims(self) -> list[Pattern]:
        """Returns a list statements for theorems that we want to publish."""
        return [self.phi0_implies_phi0, self.top()]

    def proofs(self) -> list[Proof]:
        """Returns a list of proofs for the claims."""
        return [self.imp_reflexivity(), self.top_intro()]

    def serialize(self, claims_out: BinaryIO, proofs_out: BinaryIO) -> None:
        claims_memory: list[tuple[bool, Pattern]] = []
        for claim in reversed(self.claims()):
            claim.serialize(self.notation(), set(), claims_memory, [], claims_out)
            claims_out.write(bytes([Instruction.Publish]))

        claims: list[Pattern] = self.claims()
        proofs_memory: list[tuple[bool, Pattern]] = []
        for proof in self.proofs():
            proof.serialize(self.notation(), self.lemmas(), proofs_memory, claims, proofs_out)
        assert claims == []

    # Notation
    # ========

    phi0: MetaVar = MetaVar(0)
    phi0_implies_phi0: Pattern = implies(phi0, phi0)

    def bot(self) -> Pattern:
        return Mu(SVar(0), SVar(0))

    def neg(self, p: Pattern) -> Pattern:
        return implies(p, self.bot())

    def top(self) -> Pattern:
        return self.neg(self.bot())

    # Proofs
    # ======

    # phi0 -> phi0
    def imp_reflexivity(self) -> Proof:
        return self.modus_ponens(
            self.modus_ponens(
                self.prop2().instantiate(1, self.phi0_implies_phi0).instantiate(2, self.phi0),
                self.prop1().instantiate(1, self.phi0_implies_phi0),
            ),
            self.prop1().instantiate(1, self.phi0),
        )

    # phi1 -> phi2 and phi2 -> phi3 yields also a proof of phi1 -> phi3
    def imp_transitivity(self, phi0_imp_phi1: Proof, phi1_imp_phi2: Proof) -> Proof:
        phi0_imp_phi1_conc = phi0_imp_phi1.conclusion()
        match phi0_imp_phi1_conc:
            case Implication(phi0, phi1):
                pass
            case _:
                raise AssertionError('Expected implication')
        phi1_imp_phi2_conc = phi1_imp_phi2.conclusion()
        match phi1_imp_phi2_conc:
            case Implication(phi1_r, phi2):
                assert phi1_r == phi1
            case _:
                raise AssertionError('Expected implication')

        return self.modus_ponens(
            self.modus_ponens(
                self.prop2().instantiate(1, phi1).instantiate(2, phi2).instantiate(0, MetaVar(1)),
                self.modus_ponens(self.prop1().instantiate(0, phi1_imp_phi2_conc), phi1_imp_phi2),
            ).instantiate(1, phi0),
            phi0_imp_phi1,
        )

    def top_intro(self) -> Proof:
        return self.imp_reflexivity().instantiate(0, self.bot())


if __name__ == '__main__':
    _exe, claim_path, proof_path = sys.argv
    with open(claim_path, 'wb') as claim_out:
        with open(proof_path, 'wb') as proof_out:
            Propositional().serialize(claim_out, proof_out)
