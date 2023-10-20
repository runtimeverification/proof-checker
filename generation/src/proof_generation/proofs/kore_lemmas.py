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
inhabitant_symbol = Symbol('inhabitant')
kore_next_symbol = Symbol('kore_next')
kore_dv_symbol = Symbol('kore_dv')

""" kore_top(sort) """
kore_top = Notation('kore-top', App(inhabitant_symbol, phi0), '(k⊤ {0})')

""" kore_not(sort, pattern) """
kore_not = Notation('kore-not', _and(neg(phi1), kore_top(phi0)), '(k¬ {0})')

""" kore_and(sort, pattern, pattern) """
kore_and = Notation('kore-and', _and(phi1, phi2), '({0}[{1}] k⋀ {0}[{2}])')

""" kore_or(sort, pattern, pattern) """
kore_or = Notation('kore-or', _or(phi1, phi2), '({0}[{1}] k⋁ {0}[{2}])')

""" kore_next(sort, pattern) """
kore_next = Notation('kore-next', App(kore_next_symbol, phi1), '(♦ {1})')

""" kore_implies(sort, pattern, pattern) """
kore_implies = Notation('kore-implies', kore_or(phi0, kore_not(phi0, phi1), phi2), '({0}[{1}] k-> {0}[{2}])')

""" kore_app(sorts, patterns) """
# TODO: We just drop the sort for now
# In the Kore we can have an application of a symbol to none or several arguments. We chain them manually
# in a single pattern and then save it to phi1. We can't guarantee that there are two or more args as in
# the normal application.
kore_app = Notation('kore-app', phi1, '(kapp({0}) ({1})')

""" kore_rewrites(sort, left, right) """
kore_rewrites = Notation('kore-rewrites', kore_implies(phi0, phi1, kore_next(phi0, phi2)), '({0}[{1}] k=> {0}[{2}])')

""" kore_dv(sort, value) """
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
