from __future__ import annotations

import sys
from typing import TYPE_CHECKING

from proof_generation.pattern import Implies, Symbol
from proof_generation.proof import ProofExp
from proof_generation.proofs.propositional import Propositional

if TYPE_CHECKING:
    from proof_generation.proof import ProofThunk


class SmallTheory(ProofExp):
    def __init__(self) -> None:
        super().__init__()
        self.prop = self.import_module(Propositional())
        symbol0_implies_symbol1 = Implies(Symbol('s0'), Symbol('s1'))
        symbol1_implies_symbol2 = Implies(Symbol('s1'), Symbol('s2'))
        symbol0_implies_symbol2 = Implies(Symbol('s0'), Symbol('s2'))
        self._axioms = [symbol0_implies_symbol1, symbol1_implies_symbol2]
        self._claims = [symbol0_implies_symbol2]
        self._proof_expressions = [self.sym0_implies_sym2_proof()]

    def sym0_implies_sym1(self) -> ProofThunk:
        return self.load_axiom_by_index(0)

    def sym1_implies_sym2(self) -> ProofThunk:
        return self.load_axiom_by_index(1)

    def sym0_implies_sym2_proof(self) -> ProofThunk:
        return self.prop.imp_transitivity(self.sym0_implies_sym1(), self.sym1_implies_sym2())


if __name__ == '__main__':
    SmallTheory().main(sys.argv)
