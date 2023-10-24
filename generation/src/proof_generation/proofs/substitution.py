from __future__ import annotations

import sys
from dataclasses import dataclass
from typing import TYPE_CHECKING

from proof_generation.pattern import EVar, Exists, Notation
from proof_generation.proofs.propositional import Propositional, neg, phi0, top

if TYPE_CHECKING:
    from proof_generation.pattern import Pattern
    from proof_generation.proof import Proved, ProvedExpression


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

    def proof_expressions(self) -> list[ProvedExpression]:
        return [self.top_univgen]

    def universal_gen(self, phi: ProvedExpression, var: EVar) -> Proved:
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
                self.dneg_intro(self.PROVISIONAL_get_conc(phi)),
                phi(),
            ),
            var,
        )

    def top_univgen(self) -> Proved:
        """
        T
        ---
        forall x0 . T
        """
        return self.universal_gen(self.top_intro, EVar(0))

    def functional_subst(self, phi: ProvedExpression, phi1: ProvedExpression, x: EVar) -> ProvedExpression:
        """
        --------------------------------------
        (exists x . phi1 = x) -> ((forall x. phi) -> phi[phi1/x])
        """
        raise NotImplementedError


if __name__ == '__main__':
    Substitution.main(sys.argv)
