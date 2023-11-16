from __future__ import annotations

import sys
from functools import cache
from typing import TYPE_CHECKING

from proof_generation.pattern import (
    App,
    EVar,
    Exists,
    Implies,
    Instantiate,
    MetaVar,
    Notation,
    Symbol,
    _and,
    _or,
    equiv,
    neg,
    top,
)
from proof_generation.proof import ProofExp

if TYPE_CHECKING:
    from proof_generation.pattern import Pattern

phi0 = MetaVar(0)
phi1 = MetaVar(1)
phi2 = MetaVar(2)

# TODO Add these notations to a Definedness module that also contains the definedness axiom
ceil = Notation('ceil', 1, App(top(), phi0), '⌈ {0} ⌉')
floor = Notation('floor', 1, neg(ceil(neg(phi0))), '⌊ {0} ⌋')
subset = Notation('subset', 2, floor(Implies(phi0, phi1)), '({0} ⊆ {1})')
eq = Notation('eq', 2, floor(equiv(phi0, phi1)), '({0} = {1})')
functional = Notation('functional', 1, Exists(0, eq(EVar(0), MetaVar(0, (EVar(0),)))), 'functional({0})')

# TODO: Make sure this is handled uniformly
inhabitant_symbol = Symbol('inhabitant')
kore_next_symbol = Symbol('kore_next')
kore_dv_symbol = Symbol('kore_dv')
kore_kseq_symbol = Symbol('kore_kseq')


""" kore_top(sort) """
kore_top = Notation('kore-top', 1, App(inhabitant_symbol, phi0), 'k⊤:{0}')

""" kore_not(sort, pattern) """
kore_not = Notation('kore-not', 2, _and(neg(phi1), kore_top(phi0)), '(k¬{1}):{0}')

""" kore_and(sort, pattern, pattern) """
kore_and = Notation('kore-and', 3, _and(phi1, phi2), '({1} k⋀ {2})')

""" kore_or(sort, pattern, pattern) """
kore_or = Notation('kore-or', 3, _or(phi1, phi2), '({1} k⋁ {2})')

""" kore_next(sort, pattern) """
kore_next = Notation('kore-next', 2, App(kore_next_symbol, phi1), '♦{1}')

""" kore_implies(sort, pattern, pattern) """
kore_implies = Notation('kore-implies', 3, kore_or(phi0, kore_not(phi0, phi1), phi2), '({1} k-> {2}):{0}')

""" kore_rewrites(sort, left, right) """
kore_rewrites = Notation('kore-rewrites', 3, kore_implies(phi0, phi1, kore_next(phi0, phi2)), '({1} k=> {2}):{0}')

""" kore_dv(sort, value) """
kore_dv = Notation('kore-dv', 2, App(App(kore_dv_symbol, phi0), phi1), '{1}:{0}')

# TODO: Add support for multiple apps of kseq without brackets
""" kore_kseq(left, right) """
kore_kseq = Notation('kore-kseq', 2, App(App(kore_kseq_symbol, phi0), phi1), '({0} ~> {1})')


# We can do that without worrying about the memory leaking because all notations are saved in the ProofExp object anyway.
# Note that @cache is required here as we have to return the same objects for the same arguments for notation comparisons
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


KORE_NOTATIONS = (kore_top, kore_not, kore_and, kore_or, kore_next, kore_implies, kore_rewrites, kore_dv, kore_kseq)


# TODO: Add kore-transitivity
class KoreLemmas(ProofExp):
    def __init__(self) -> None:
        super().__init__(notations=list(KORE_NOTATIONS))


if __name__ == '__main__':
    KoreLemmas().main(sys.argv)
