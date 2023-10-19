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
        return f'(\u2200 x{self.var} . {str(self.phi0)})'


class Substitution(Propositional):
    @staticmethod
    def axioms() -> list[Pattern]:
        return []

    @staticmethod
    def claims() -> list[Pattern]:
        return []

    def proof_expressions(self) -> list[ProvedExpression]:
        return []

    def universal_gen(self, phi: MetaVar) -> ProvedExpression:
        """
        phi
        --------------------------------------
        forall x . phi
        """
        return lambda: ret

    def functional_subst(self, phi: MetaVar, phi1: MetaVar, x: EVar) -> ProvedExpression:
        """
        --------------------------------------
        (exists x . phi1 = x) -> ((forall x. phi) -> phi[phi1/x])
        """
        ret =

        return lambda: ret


if __name__ == '__main__':
    SmallTheory.main(sys.argv)
