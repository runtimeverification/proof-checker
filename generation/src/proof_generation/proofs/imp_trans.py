from __future__ import annotations

import sys
from typing import TYPE_CHECKING

from proof_generation.proof import Implication, Symbol
from proof_generation.proofs.propositional import Propositional, neg, bot, phi0, phi1, phi2

if TYPE_CHECKING:
    from proof_generation.proof import Pattern, Proved, ProvedExpression


class ImpTrans(Propositional):
    @staticmethod
    def axioms() -> list[Pattern]:
        imp_trans = Implication(Implication(phi0, phi1), Implication(Implication(phi1, phi2), Implication(phi0, phi2)))
        return [imp_trans]

    @staticmethod
    def claims() -> list[Pattern]:
        contrapositive_claim = Implication(Implication(phi0, phi1), Implication(neg(phi1), neg(phi0)))
        return [contrapositive_claim]

    def proof_expressions(self) -> list[ProvedExpression]:
        return [self.sym0_implies_sym2_proof]

    def imp_trans(self) -> Proved:
        return self.load_axiom(self.axioms()[0])

    def contrapositive(self) -> Proved:
        return self.imp_trans().instantiate( {0: phi0, 1: phi1, 2: bot} )


if __name__ == '__main__':
    ImpTrans.main(sys.argv)
