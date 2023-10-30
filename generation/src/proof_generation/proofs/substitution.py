from __future__ import annotations

import sys
from typing import TYPE_CHECKING

from proof_generation.pattern import EVar, Exists, Notation
from proof_generation.proofs.propositional import Propositional, neg, phi0, top

if TYPE_CHECKING:
    from proof_generation.pattern import Pattern
    from proof_generation.proof import ProofThunk


def forall(var: int) -> Notation:
    return Notation(f'forall_{var}', neg(Exists(var, neg(phi0))), f'(∀ x{var} . {{0}})')


class Substitution(Propositional):
    @staticmethod
    def axioms() -> list[Pattern]:
        return []

    @staticmethod
    def claims() -> list[Pattern]:
        return [forall(0)(top())]

    def proof_expressions(self) -> list[ProofThunk]:
        return [self.top_univgen()]

    def universal_gen(self, phi: ProofThunk, var: EVar) -> ProofThunk:
        """
        phi
        --------------------------------------
        forall {var} . phi
        """
        # (exists {var} (neg phi)) -> bot == forall {var} phi
        return self.exists_generalization(
            # neg phi -> bot
            self.modus_ponens(
                # phi -> (neg phi -> bot)
                self.dneg_intro(phi.conc),
                phi,
            ),
            var,
        )

    def top_univgen(self) -> ProofThunk:
        """
        T
        ---
        forall x0 . T
        """
        return self.universal_gen(self.top_intro(), EVar(0))

    def functional_subst(self, phi: ProofThunk, phi1: ProofThunk, x: EVar) -> ProofThunk:
        """
        --------------------------------------
        (exists x . phi1 = x) -> ((forall x. phi) -> phi[phi1/x])
        """
        raise NotImplementedError


if __name__ == '__main__':
    Substitution.main(sys.argv)
