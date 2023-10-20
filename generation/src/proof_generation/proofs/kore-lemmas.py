from __future__ import annotations

import sys
from typing import TYPE_CHECKING

from proof_generation.pattern import App, MetaVar, Notation, Symbol
from proof_generation.proof import ProofExp
from proof_generation.proofs.propositional import _and, _or, neg

if TYPE_CHECKING:
    from proof_generation.pattern import Pattern
    from proof_generation.proof import ProvedExpression

phi0 = MetaVar(0)
phi1 = MetaVar(1)
phi2 = MetaVar(2)

# TODO: Make sure this is handled uniformly
inhabitant_symbol = Symbol(0)
kore_next_symbol = Symbol(1)
kore_dv_symbol = Symbol(2)

kore_top = Notation('kore-top', App(inhabitant_symbol, phi0), '(k⊤ {0})')
kore_not = Notation('kore-not', _and(neg(phi1), kore_top(phi0)), '(k¬ {0})')
kore_and = Notation('kore-and', _and(phi1, phi2), '({0}[{1}] k⋀ {0}[{2}])')
kore_or = Notation('kore-or', _or(phi1, phi2), '({0}[{1}] k⋁ {0}[{2}])')
kore_next = Notation('kore-next', App(kore_next_symbol, phi1), '(♦ {str(self.phi1)})')
kore_implies = Notation('kore-implies', kore_or(phi0, kore_not(phi0, phi1), phi2), '({0}[{1}] k-> {0}[{2}])')
kore_rewrites = Notation(
    'kore-rewrites',
    kore_implies(phi0, phi1, kore_next(phi0, phi2)),
    '({str(self.phi0)}[{str(self.phi1)}] k=> {str(self.phi0)}[{str(self.phi2)}])',
)
kore_dv = Notation('kore-dv', App(App(kore_dv_symbol, phi0), phi1), 'dv({0})')


# TODO: Add kore-transitivity
class KoreLemmas(ProofExp):
    @staticmethod
    def axioms() -> list[Pattern]:
        return []

    @staticmethod
    def claims() -> list[Pattern]:
        return []

    def proof_expressions(self) -> list[ProvedExpression]:
        return []


if __name__ == '__main__':
    KoreLemmas.main(sys.argv)
