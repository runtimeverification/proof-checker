from __future__ import annotations

import sys
from typing import TYPE_CHECKING

from proof_generation.pattern import Implication, EVar
from proof_generation.proofs.propositional import Propositional, neg, phi0

if TYPE_CHECKING:
    from proof_generation.pattern import Pattern
    from proof_generation.proof import ProvedExpression
    from proof_generation.proved import Proved


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

    def dneg_intro(self, a: Pattern) -> ProvedExpression:
        return lambda: self.dynamic_inst(
            self.load_axiom(self.axioms[0]), {0: a}
        )

    def universal_gen(self, phi: ProvedExpression, var: EVar) -> ProvedExpression:
        """
        phi
        --------------------------------------
        forall {var} . phi
        """
        return self.dynamic_inst(
            # (exists {var} (neg phi)) -> bot == forall {var} phi
            self.exists_generalization(
                # neg phi -> bot
                self.modus_ponens(
                    # phi -> (neg phi -> bot)
                    self.dneg_intro(self.PROVISIONAL_get_conc(phi)),
                    phi()
                ),
                bot,
                var
            )
        )

    def functional_subst(self, phi: ProvedExpression, phi1: ProvedExpression, x: EVar) -> ProvedExpression:
        """
        --------------------------------------
        (exists x . phi1 = x) -> ((forall x. phi) -> phi[phi1/x])
        """
        raise NotImplementedError


if __name__ == '__main__':
    Substitution.main(sys.argv)
