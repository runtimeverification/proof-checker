from __future__ import annotations

import sys
from dataclasses import dataclass
from typing import TYPE_CHECKING

from proof_generation.pattern import ESubst, EVar, Exists, Implies, Notation
from proof_generation.proofs.propositional import Equiv, Propositional, neg, phi0, phi1, top

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


x = EVar(0)


class Substitution(Propositional):
    @staticmethod
    def axioms() -> list[Pattern]:
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

    def functional_subst(self, psi: Pattern = phi1, phi: Pattern = phi0, x: EVar = x) -> Proved:
        """
        ------------------------------------------------------
        (exists x . psi <-> x) -> ((forall x. phi) -> phi[psi/x])
        """
        return self.dynamic_inst(lambda: self.load_axiom(self.axioms()[0]), {0: phi, 1: psi})

    def apply_subst(self, psi_func_pr: ProvedExpression, phi_pr: ProvedExpression) -> Proved:
        """
        (exists x . psi <-> x)                  (forall x. phi)
        ------------------------------------------------------
        phi[psi/x]
        """
        psi = self.PROVISIONAL_get_conc(psi_func_pr)
        phi = self.PROVISIONAL_get_conc(phi_pr)
        return self.modus_ponens(self.modus_ponens(self.functional_subst(psi, phi), psi_func_pr()), phi_pr())


if __name__ == '__main__':
    Substitution.main(sys.argv)
