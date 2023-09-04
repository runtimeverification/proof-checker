from __future__ import annotations

import sys
from typing import TYPE_CHECKING

from proof_generation.proof import Implication, Proved, Symbol
from proof_generation.proofs.propositional import Propositional

if TYPE_CHECKING:
    from proof_generation.proof import Pattern, ProvedExpression


class SmallTheory(Propositional):
    @staticmethod
    def axioms() -> list[Pattern]:
        phi0_implies_phi1 = Implication(Symbol(0), Symbol(1))
        phi1_implies_phi2 = Implication(Symbol(1), Symbol(2))
        return [phi0_implies_phi1, phi1_implies_phi2]

    # Convert a term to an axiom, providing the interpreter
    def hydrate(self, term: Pattern) -> Proved:
        return Proved(self.interpreter, term)

    @staticmethod
    def claims() -> list[Pattern]:
        phi0_implies_phi2 = Implication(Symbol(0), Symbol(2))
        return [phi0_implies_phi2]

    def proof_expressions(self) -> list[ProvedExpression]:
        return [self.sym0_implies_sym2_proof]

    def sym0(self) -> Pattern:
        if ret := self.load_notation('sym0'):
            return ret
        return self.save_notation('sym0', self.symbol(0))

    def sym1(self) -> Pattern:
        if ret := self.load_notation('sym1'):
            return ret
        return self.save_notation('sym1', self.symbol(1))

    def sym2(self) -> Pattern:
        if ret := self.load_notation('sym2'):
            return ret
        return self.save_notation('sym2', self.symbol(2))

    def sym0_implies_sym1(self) -> Proved:
        term = self.hydrate(self.axioms()[0])
        return term

    def sym1_implies_sym2(self) -> Proved:
        term = self.hydrate(self.axioms()[1])
        return term

    def sym0_implies_sym2(self) -> Pattern:
        if ret := self.load_notation('sym0_implies_sym2'):
            return ret
        return self.save_notation('sym0_implies_smy2', self.implies(self.sym0(), self.sym2()))

    def sym0_implies_sym2_proof(self) -> Proved:
        return super().imp_transitivity(self.sym0_implies_sym1(), self.sym1_implies_sym2())


if __name__ == '__main__':
    SmallTheory.main(sys.argv)
