from __future__ import annotations

import sys
from typing import TYPE_CHECKING
from dataclasses import dataclass

from proof_generation.pattern import Implies, Notation, Exists
from proof_generation.proofs.propositional import Propositional, neg, phi0

if TYPE_CHECKING:
    from proof_generation.pattern import Pattern, EVar
    from proof_generation.proof import ProvedExpression, Proved


@dataclass(frozen=True, eq=False)
class Forall(Notation):
    var: int
    phi0: Pattern

    def definition(self) -> Pattern:
        return neg(Exists(self.var, neg(phi0)))

    def __str__(self) -> str:
        return f'(∀ x{self.var} . {str(self.phi0)})'


class Substitution(Propositional):
    @staticmethod
    def axioms() -> list[Pattern]:
        return [
            Implies(phi0, neg(neg(phi0))),  # Double Negation Intro
        ]

    @staticmethod
    def claims() -> list[Pattern]:
        return []

    def proof_expressions(self) -> list[ProvedExpression]:
        return []

    def dneg_intro(self, a: Pattern) -> Proved:
        return self.dynamic_inst(
            lambda: self.load_axiom(self.axioms()[0]), {0: a}
        )

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
                phi()
            ),
            var
        )

    def functional_subst(self, phi: ProvedExpression, phi1: ProvedExpression, x: EVar) -> ProvedExpression:
        """
        --------------------------------------
        (exists x . phi1 = x) -> ((forall x. phi) -> phi[phi1/x])
        """
        raise NotImplementedError


if __name__ == '__main__':
    Substitution.main(sys.argv)
