from __future__ import annotations

import sys
from dataclasses import dataclass
from typing import TYPE_CHECKING

from proof_generation.pattern import EVar, Exists, Notation
from proof_generation.proof import ProofThunk
from proof_generation.proofs.propositional import Propositional, neg, phi0, top

if TYPE_CHECKING:
    from proof_generation.pattern import Pattern


@dataclass(frozen=True, eq=False)
class Forall(Notation):
    var: int
    phi0: Pattern

    def object_definition(self) -> Pattern:
        return neg(Exists(self.var, neg(phi0)))

    def __str__(self) -> str:
        return f'(∀ x{self.var} . {str(self.phi0)})'


class Substitution(Propositional):
    @staticmethod
    def axioms() -> list[Pattern]:
        return []

    @staticmethod
    def claims() -> list[Pattern]:
        return [Forall(0, top)]

    def proof_expressions(self) -> list[ProofThunk]:
        return [self.top_univgen()]

    def universal_gen(self, phi: ProofThunk, var: EVar) -> ProofThunk:
        """
        phi
        --------------------------------------
        forall {var} . phi
        """
        # (exists {var} (neg phi)) -> bot == forall {var} phi
        return ProofThunk(
            (
                lambda: self.exists_generalization(
                    # neg phi -> bot
                    self.mp(
                        # phi -> (neg phi -> bot)
                        self.dneg_intro(phi.conc),
                        phi,
                    )(),
                    var,
                )
            ),
            Forall(var.name, phi.conc),
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
