from __future__ import annotations

import sys
from functools import cache
from typing import TYPE_CHECKING

from proof_generation.pattern import App, EVar, Exists, Instantiate, MetaVar, Notation, Symbol, _and, _or, bot, neg
from proof_generation.proof import ProofExp
from proof_generation.proofs.definedness import Definedness, ceil, subset

if TYPE_CHECKING:
    from proof_generation.pattern import Pattern

phi0 = MetaVar(0)
phi1 = MetaVar(1)
phi2 = MetaVar(2)
phi3 = MetaVar(3)

# TODO: Make sure this is handled uniformly
inhabitant_symbol = Symbol('inhabitant')
kore_next_symbol = Symbol('kore_next')
kore_dv_symbol = Symbol('kore_dv')
kore_kseq_symbol = Symbol('kore_kseq')

in_sort = Notation('in-sort', 2, subset(phi0, App(inhabitant_symbol, phi1)), '{0}:{1}')


@cache
def sorted_exists(var: int) -> Notation:
    """sorted_exists(inner_sort, pattern)"""
    # TODO: Don't forget to save the result of the function call to a proof expression object
    return Notation('sorted-exists', 2, Exists(var, _and(in_sort(EVar(var), phi0), phi1)), f'( ∃ x{var}:{0} . {1} )')


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
kore_dv = Notation('kore-dv', 2, App(App(kore_dv_symbol, phi0), phi1), 'dv({1}):{0}')

""" kore_ceil(inner_sort, outer_sort, pattern) """
kore_ceil = Notation('kore-ceil', 3, _and(ceil(phi2), kore_top(phi1)), 'k⌈ {2}:{0} ⌉:{1}')

""" kore_floor(inner_sort, outer_sort, pattern) """
kore_floor = Notation('kore-floor', 3, kore_not(phi1, kore_ceil(phi0, phi1, kore_not(phi0, phi2))), 'k⌊ {2}:{0} ⌋:{1}')

""" kore_iff(sort, left, right) """
kore_iff = Notation(
    'kore-iff', 3, kore_and(phi0, kore_implies(phi0, phi1, phi2), kore_implies(phi0, phi2, phi1)), '({1} k<-> {2}):{0}'
)

""" kore_equals(inner_sort, outer_sort, left, right) """
kore_equals = Notation('kore-equals', 4, kore_floor(phi0, phi1, kore_iff(phi0, phi2, phi3)), '({2}:{0} k= {3}:{0}):{1}')

# TODO: Add support for multiple apps of kseq without brackets
""" kore_kseq(left, right) """
kore_kseq = Notation('kore-kseq', 2, App(App(kore_kseq_symbol, phi0), phi1), '({0} ~> {1})')

""" kore_in(inner_sort, outer_sort, left, right) """
kore_in = Notation('kore-in', 4, kore_floor(phi0, phi1, kore_implies(phi0, phi2, phi3)), '({2}:{0}} k⊆ {3}:{0}):{1}')

""" kore_bottom(sort) """
kore_bottom = Notation('kore-bottom', 1, bot(), 'k⊥')


@cache
def kore_exists(var: int) -> Notation:
    """kore_exists(variable_sort, outer_sort, pattern)"""
    # TODO: Don't forget to save the result of the function call to a proof expression object
    return Notation(
        'kore-exists',
        3,
        _and(sorted_exists(var)(phi0, phi2), App(inhabitant_symbol, phi1)),
        '( k∃ {var}:{0} . {2}):{1}',
    )


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


KORE_NOTATIONS = (
    kore_top,
    kore_not,
    kore_and,
    kore_or,
    kore_next,
    kore_implies,
    kore_rewrites,
    kore_dv,
    kore_ceil,
    kore_floor,
    kore_iff,
    kore_equals,
    kore_kseq,
    kore_in,
    kore_bottom,
    in_sort,
)


# TODO: Add kore-transitivity
class KoreLemmas(ProofExp):
    def __init__(self) -> None:
        super().__init__(notations=list(KORE_NOTATIONS))
        self.definedness = self.import_module(Definedness())


if __name__ == '__main__':
    KoreLemmas().main(sys.argv)
