from __future__ import annotations

import sys
from functools import cache
from typing import TYPE_CHECKING

from proof_generation.pattern import App, Instantiate, MetaVar, Notation, Symbol
from proof_generation.proof import ProofExp
from proof_generation.proofs.propositional import _and, _or, neg

if TYPE_CHECKING:
    from proof_generation.pattern import Pattern

phi0 = MetaVar(0)
phi1 = MetaVar(1)
phi2 = MetaVar(2)


# TODO: Make sure this is handled uniformly
inhabitant_symbol = Symbol('inhabitant')
kore_next_symbol = Symbol('kore_next')
kore_dv_symbol = Symbol('kore_dv')


""" kore_top(sort) """
kore_top = Notation('kore-top', 1, App(inhabitant_symbol, phi0), 'k{0}[⊤]')

""" kore_not(sort, pattern) """
kore_not = Notation('kore-not', 2, _and(neg(phi1), kore_top(phi0)), 'k¬{0}[{1}]')

""" kore_and(sort, pattern, pattern) """
kore_and = Notation('kore-and', 3, _and(phi1, phi2), '({1} k⋀ {2})')

""" kore_or(sort, pattern, pattern) """
kore_or = Notation('kore-or', 3, _or(phi1, phi2), '({1} k⋁ {2})')

""" kore_next(sort, pattern) """
kore_next = Notation('kore-next', 2, App(kore_next_symbol, phi1), '♦{0}')

""" kore_implies(sort, pattern, pattern) """
kore_implies = Notation('kore-implies', 3, kore_or(phi0, kore_not(phi0, phi1), phi2), '({0}[{1}] k-> {0}[{2}])')

""" kore_rewrites(sort, left, right) """
kore_rewrites = Notation('kore-rewrites', 3, kore_implies(phi0, phi1, kore_next(phi0, phi2)), '({0}[{1}] k=> {0}[{2}])')

""" kore_dv(sort, value) """
kore_dv = Notation('kore-dv', 2, App(App(kore_dv_symbol, phi0), phi1), '{1}:{0}')


# We can do that without worrying about the memory leaking because all notations are saved in the ProofExp object anyway.
@cache
def nary_app(symbol: Symbol, n: int, cell: bool = False) -> Notation:
    """Constructs an nary application."""
    p: Pattern = symbol
    fmt_args: list[str] = []
    for i in range(0, n):
        p = App(p, MetaVar(i))
        fmt_args.append('{' + str(i) + '}')

    fmt: str
    if cell:
        fmt = f'<{symbol.name}> ' + ' '.join(fmt_args) + f' </{symbol.name}>'
    else:
        fmt = f'{symbol.name}(' + ', '.join(fmt_args) + ')'

    return Notation(symbol.name, n, p, fmt)


def nary_cell(symbol: Symbol, n: int) -> Notation:
    return nary_app(symbol, n, cell=True)


def deconstruct_nary_application(p: Pattern) -> tuple[Pattern, tuple[Pattern, ...]]:
    match p:
        case Instantiate(_, _):
            # TODO: Consider something smarter here.
            return deconstruct_nary_application(p.simplify())
        case App(l, r):
            symbol, args = deconstruct_nary_application(l)
            return symbol, (*args, r)
        case _:
            return p, ()


KORE_NOTATIONS = (
    kore_top,
    kore_not,
    kore_and,
    kore_or,
    kore_next,
    kore_implies,
    kore_rewrites,
    kore_dv,
)


# TODO: Add kore-transitivity
class KoreLemmas(ProofExp):
    def __init__(self) -> None:
        super().__init__(notations=list(KORE_NOTATIONS))


if __name__ == '__main__':
    KoreLemmas().main(sys.argv)
