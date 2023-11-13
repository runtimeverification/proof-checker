from __future__ import annotations

import sys
from typing import TYPE_CHECKING

from proof_generation.pattern import Implies, Symbol
from proof_generation.proofs.propositional import Propositional

if TYPE_CHECKING:
    from proof_generation.pattern import Pattern
    from proof_generation.proof import ProofThunk


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

    def proof_expressions(self) -> list[ProofThunk]:
        return [self.sym0_implies_sym2_proof()]

    def sym0_implies_sym1(self) -> ProofThunk:
        return self.load_axiom_by_index(0)

    def sym1_implies_sym2(self) -> ProofThunk:
        return self.load_axiom_by_index(1)

    def sym0_implies_sym2_proof(self) -> ProofThunk:
        return self.imp_transitivity(self.sym0_implies_sym1(), self.sym1_implies_sym2())


if __name__ == '__main__':
    SmallTheory.main(sys.argv)
