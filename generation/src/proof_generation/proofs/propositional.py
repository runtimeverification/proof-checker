from __future__ import annotations

import sys
from typing import TYPE_CHECKING, BinaryIO

from proof_generation.instruction import Instruction
from proof_generation.proof import Implication, MetaVar, ModusPonens, Mu, Prop1, Prop2, Prop3, SVar, implies, neg, bot

if TYPE_CHECKING:
    from proof_generation.proof import Pattern, Proof


class ProofExp:
    def prop1(self) -> Proof:
        return Prop1()

    def prop2(self) -> Proof:
        return Prop2()

    def prop3(self) -> Proof:
        return Prop3()

    def modus_ponens(self, left: Proof, right: Proof) -> Proof:
        """This wrapper flips the order of arguments for modus ponens,
        so that ITP proof scripts from the proof-generation repo look the same."""
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
        return {self.phi0, bot(), self.top, self.phi0_implies_phi0}

    def claims(self) -> list[Pattern]:
        """Returns a list statements for theorems that we want to publish."""
        return [self.phi0_implies_phi0, self.top, self.bot_implies_phi0]

    def proofs(self) -> list[Proof]:
        """Returns a list of proofs for the claims."""
        return [self.imp_reflexivity(), self.top_intro(), self.bot_elim()]

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
    top: Pattern = neg(bot())
    bot_implies_phi0 = implies(bot(), phi0)

    # Proofs
    # ======

    # phi0 -> phi0
    def imp_reflexivity(self) -> Proof:
        return self.modus_ponens(
            self.modus_ponens(
                self.prop2().instantiate((1, 2), (self.phi0_implies_phi0, self.phi0)),
                self.prop1().instantiate((1,), (self.phi0_implies_phi0,)),
            ),
            self.prop1().instantiate((1,), (self.phi0,)),
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
                self.prop2().instantiate((1, 2, 0), (phi1, phi2, MetaVar(1))),
                self.modus_ponens(self.prop1().instantiate((0,), (phi1_imp_phi2_conc,)), phi1_imp_phi2),
            ).instantiate((1,), (phi0,)),
            phi0_imp_phi1,
        )

    def top_intro(self) -> Proof:
        return self.imp_reflexivity().instantiate((0,), (bot(),))

    def bot_elim(self) -> Proof:
        # neg neg 0 -> 0
        pat1 = implies(neg(neg(self.phi0)), self.phi0)
        # neg neg 2
        pat2 = neg(neg(self.phi0))

        return self.modus_ponens(
            # ((bot -> neg neg 0) -> (bot -> 0)))
            self.modus_ponens(
                # (bot -> (neg neg 0 -> 0)) -> ((bot -> neg neg 0) -> (bot -> 0))
                self.prop2().instantiate((0, 1, 2), (bot(), pat2, self.phi0)),
                # (bot -> (neg neg 0 -> 0))
                self.modus_ponens(
                    # (neg neg 0 -> 0) -> (bot -> (neg neg 0 -> 0))
                    self.prop1().instantiate((0, 1), (pat1, bot())),
                    # (neg neg 0 -> 0)
                    self.prop3().instantiate((0,), (self.phi0,)),
                ),
            ),
            # (bot -> (neg phi0 -> bot))
            self.prop1().instantiate((0, 1), (bot(), neg(self.phi0))),
        )


if __name__ == '__main__':
    _exe, claim_path, proof_path = sys.argv
    with open(claim_path, 'wb') as claim_out:
        with open(proof_path, 'wb') as proof_out:
            Propositional().serialize(claim_out, proof_out)
