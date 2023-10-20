from __future__ import annotations

import sys
from typing import TYPE_CHECKING

from proof_generation.pattern import Implies, Symbol
from proof_generation.proofs.propositional import Propositional

if TYPE_CHECKING:
    from proof_generation.pattern import Pattern
    from proof_generation.proof import ProvedExpression
    from proof_generation.proved import Proved


class SmallTheory(Propositional):
    @staticmethod
    def axioms() -> list[Pattern]:
        symbol0_implies_symbol1 = Implies(Symbol('s0'), Symbol('s1'))
        symbol1_implies_symbol2 = Implies(Symbol('s1'), Symbol('s2'))
        return [symbol0_implies_symbol1, symbol1_implies_symbol2]

    @staticmethod
    def claims() -> list[Pattern]:
        symbol0_implies_symbol2 = Implies(Symbol('s0'), Symbol('s2'))
        return [symbol0_implies_symbol2]

    def proof_expressions(self) -> list[ProvedExpression]:
        return [self.sym0_implies_sym2_proof]

    def sym0_implies_sym1(self) -> Proved:
        return self.load_axiom(self.axioms()[0])

    def sym1_implies_sym2(self) -> Proved:
        return self.load_axiom(self.axioms()[1])

    def sym0_implies_sym2_proof(self) -> Proved:
        return super().imp_transitivity(self.sym0_implies_sym1, self.sym1_implies_sym2)


if __name__ == '__main__':
    SmallTheory.main(sys.argv)
