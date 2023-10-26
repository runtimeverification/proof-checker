from __future__ import annotations

import sys
from dataclasses import dataclass
from typing import TYPE_CHECKING

from proof_generation.pattern import EVar, Exists, Notation, ESubst
from proof_generation.proofs.propositional import Propositional, neg, phi0, phi1, top, Equiv

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
        x = EVar(0)
        return [
            # TODO: Replace Equiv with =
            Implies(Exists(x.name, Equiv(phi1, x)), Implies(Forall(x.name, phi0), ESubst(phi0, x, phi1)))
        ]

    @staticmethod
    def claims() -> list[Pattern]:
        return [Forall(0, top)]

    def proof_expressions(self) -> list[ProvedExpression]:
        return [self.top_univgen]

    def universal_gen(self, phi: ProvedExpression, var: EVar) -> Proved:
        """
               phi
        ------------------
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
        -------------
        forall x0 . T
        """
        return self.universal_gen(self.top_intro, EVar(0))

    def functional_subst(self, phi: ProvedExpression, psi: ProvedExpression, x: EVar) -> ProvedExpression:
        """
        ------------------------------------------------------
        (exists x . psi = x) -> ((forall x. phi) -> phi[psi/x])
        """
        return self.dynamic_inst(
            self.load_axiom(self.axioms()[0]),
            {0: phi, 1: psi}
        )


if __name__ == '__main__':
    Substitution.main(sys.argv)
