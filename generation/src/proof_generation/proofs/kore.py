from __future__ import annotations

import sys
from functools import cache
from typing import TYPE_CHECKING

from proof_generation.aml import App, EVar, Exists, Implies, Instantiate, MetaVar, Notation, Symbol, _and, _or, bot, neg
from proof_generation.proof import ProofExp
from proof_generation.proofs.definedness import Definedness, ceil, subset
from proof_generation.proofs.substitution import HOLE

if TYPE_CHECKING:
    from proof_generation.aml import Pattern
    from proof_generation.proof import ProofThunk

phi0 = MetaVar(0)
phi1 = MetaVar(1)
phi2 = MetaVar(2)
phi3 = MetaVar(3)
phi4 = MetaVar(4)

# TODO: Make sure this is handled uniformly
inhabitant_symbol = Symbol('inhabitant')
kore_next_symbol = Symbol('kore_next')
kore_dv_symbol = Symbol('kore_dv')
kore_kseq_symbol = Symbol('kore_kseq')

""" in_sort(element, sort) """
in_sort = Notation('in-sort', 2, subset(phi0, App(inhabitant_symbol, phi1)), '{0}:{1}')


@cache
def sorted_exists(var: int) -> Notation:
    """sorted_exists(inner_sort, pattern)"""
    # TODO: It is not included in any KORE.notations
    return Notation('sorted-exists', 2, Exists(var, _and(in_sort(EVar(var), phi0), phi1)), f'( ∃ x{var}:{0} . {1} )')


""" kore_top(sort) """
kore_top = Notation('kore-top', 1, App(inhabitant_symbol, phi0), 'k⊤:{0}')

""" kore_not(sort, pattern) """
kore_not = Notation('kore-not', 2, _and(neg(phi1), kore_top(phi0)), '(k¬{1}):{0}')

""" kore_and(pattern, pattern) """
kore_and = Notation('kore-and', 2, _and(phi0, phi1), '({0} k⋀ {1})')

""" kore_or(pattern, pattern) """
kore_or = Notation('kore-or', 2, _or(phi0, phi1), '({0} k⋁ {1})')

""" kore_next(pattern) """
kore_next = Notation('kore-next', 1, App(kore_next_symbol, phi0), '♦{0}')

""" kore_implies(sort, pattern, pattern) """
kore_implies = Notation('kore-implies', 3, kore_or(kore_not(phi0, phi1), phi2), '({1} k-> {2}):{0}')

""" kore_rewrites(sort, left, right) """
kore_rewrites = Notation('kore-rewrites', 3, kore_implies(phi0, phi1, kore_next(phi2)), '({1} k=> {2}):{0}')

""" kore_dv(sort, value) """
kore_dv = Notation('kore-dv', 2, App(App(kore_dv_symbol, phi0), phi1), 'dv({1}):{0}')

""" kore_ceil(inner_sort, outer_sort, pattern) """
kore_ceil = Notation('kore-ceil', 3, _and(ceil(phi2), kore_top(phi1)), 'k⌈ {2}:{0} ⌉:{1}')

""" kore_floor(inner_sort, outer_sort, pattern) """
kore_floor = Notation('kore-floor', 3, kore_not(phi1, kore_ceil(phi0, phi1, kore_not(phi0, phi2))), 'k⌊ {2}:{0} ⌋:{1}')

""" kore_iff(sort, left, right) """
kore_iff = Notation(
    'kore-iff', 3, kore_and(kore_implies(phi0, phi1, phi2), kore_implies(phi0, phi2, phi1)), '({1} k<-> {2}):{0}'
)

""" kore_equals(inner_sort, outer_sort, left, right) """
kore_equals = Notation('kore-equals', 4, kore_floor(phi0, phi1, kore_iff(phi0, phi2, phi3)), '({2}:{0} k= {3}:{0}):{1}')

# TODO: Add support for multiple apps of kseq without brackets
""" kore_kseq(left, right) """
kore_kseq = Notation('kore-kseq', 2, App(App(kore_kseq_symbol, phi0), phi1), '({0} ~> {1})')

""" kore_in(inner_sort, outer_sort, left, right) """
kore_in = Notation('kore-in', 4, kore_floor(phi0, phi1, kore_implies(phi0, phi2, phi3)), '({2}:{0} k⊆ {3}:{0}):{1}')

""" kore_bottom() """
kore_bottom = Notation('kore-bottom', 0, bot(), 'k⊥')

""" equational-as(inner_sort, outer_sort, from_evar, expression, to_evar) """
kore_equational_as = Notation(
    'kore-equational-as', 5, kore_in(phi0, phi1, phi2, kore_and(phi3, phi4)), '({2}:{0} k⊆ ({3} k⋀ {4}):{0}):{1}'
)


@cache
def kore_exists(var: int) -> Notation:
    """kore_exists(inner_sort, outer_sort, pattern)"""
    return Notation(
        'kore-exists',
        3,
        _and(sorted_exists(var)(phi0, phi2), App(inhabitant_symbol, phi1)),
        f'( k∃ {var}:{0} . {2}):{1}',
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


@cache
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


@cache
def deconstruct_equality_rule(pattern: Pattern) -> tuple[Pattern, Pattern, Pattern, Pattern, Pattern]:
    _, requires, imp_right = kore_implies.assert_matches(pattern)
    _, _, eq_left, eq_right_and_ensures = kore_equals.assert_matches(imp_right)

    # TODO: Potentially there can be more than one arg, but we have an assertion at converting kore patterns to catch such cases
    eq_right, ensures = kore_and.assert_matches(eq_right_and_ensures)
    return requires, eq_left, eq_right_and_ensures, eq_right, ensures


@cache
def matching_requires_substitution(pattern: Pattern) -> dict[int, Pattern]:
    collected_substitutions: dict[int, Pattern] = {}

    if top_and_match := kore_and.matches(pattern):
        left, right = top_and_match

        for item in (left, right):
            if let_match := kore_equational_as.matches(item):
                _, _, from_evar, expression, to_evar = let_match
                if isinstance(from_evar, EVar) and isinstance(to_evar, EVar) and from_evar.name != to_evar.name:
                    collected_substitutions[from_evar.name] = expression
                    collected_substitutions[to_evar.name] = expression
            elif in_match := kore_in.matches(item):
                _, _, var, expression = in_match
                if isinstance(var, EVar):
                    collected_substitutions[var.name] = expression
            else:
                collected_substitutions.update(matching_requires_substitution(item))

    return collected_substitutions


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

# TODO: Prove the axiom
# (phi2:{phi0} k= phi3:{phi0}):{phi1} -> (phi4[phi2/x]:{phi0} k= phi4[phi3/x]:{phi0}):{phi1}
keq_substitution_axiom = Implies(
    kore_equals(phi0, phi1, phi2, phi3),
    kore_equals(
        phi0,
        phi1,
        MetaVar(4, app_ctx_holes=(HOLE,)).apply_esubst(HOLE.name, phi2),
        MetaVar(4, app_ctx_holes=(HOLE,)).apply_esubst(HOLE.name, phi3),
    ),
)

# TODO: Requires a proof
# (phi1 k= phi2 k/\ k⊤:{phi0}):{phi1}
right_top_in_eq_axiom = Implies(
    kore_equals(phi0, phi1, phi2, kore_and(phi3, kore_top(phi0))), kore_equals(phi0, phi1, phi2, phi3)
)

# TODO: Requires a proof
# ((k⊤:{phi0} k/\ phi1:{phi0}) k-> phi2):{phi0} -> (phi1:{phi0} k-> phi2)):{phi0}
left_top_in_imp_axiom = Implies(
    kore_implies(phi0, kore_and(kore_top(phi0), phi1), phi2), kore_implies(phi0, phi1, phi2)
)

# TODO: Requires a proof
# ((phi1:{phi0} k/\ k⊤:{phi0}) k-> phi2):{phi0} -> (phi1:{phi0} k-> phi2)):{phi0}
remove_top_imp_right_axiom = Implies(
    kore_implies(phi0, kore_and(phi1, kore_top(phi0)), phi2), kore_implies(phi0, phi1, phi2)
)

# TODO: Requires a proof
# (phi2:{phi0} k⊆ (phi2 k/\ phi2):{phi0}):{phi1} k-> phi3):{phi1} -> phi3
reduce_equational_as_axiom = Implies(kore_implies(phi1, kore_equational_as(phi0, phi1, phi2, phi2, phi2), phi3), phi3)

# TODO: Requires a proof
# (phi2:{phi0} k⊆ phi2:{phi0} k-> phi3):{phi1} -> phi3
reduce_in_axiom = Implies(kore_implies(phi1, kore_in(phi0, phi1, phi2, phi2), phi3), phi3)

# TODO: Requires a proof
# (k⊤:{phi0} k-> phi1):{phi0}
reduce_top_axiom = Implies(kore_implies(phi0, kore_top(phi0), phi1), phi1)

# TODO: Prove the axiom
# (phi2:{phi0} k= phi3:{phi0}):{phi1} -> ( ♦(phi4[phi2/x]):{phi0} k= ♦(phi4[phi3/x]):{phi0} ):{phi1}
keq_next_substitution_axiom = Implies(
    kore_equals(phi0, phi1, phi2, phi3),
    kore_equals(
        phi0,
        phi1,
        kore_next(MetaVar(4, app_ctx_holes=(HOLE,)).apply_esubst(HOLE.name, phi2)),
        kore_next(MetaVar(4, app_ctx_holes=(HOLE,)).apply_esubst(HOLE.name, phi3)),
    ),
)

# TODO: Prove the axiom
# (phi2:{phi0} k= phi3:{phi0}):{phi1} -> ((phi4 k-> phi2):{phi1} -> (phi4 k-> phi3):{phi1})
keq_implication_axiom = Implies(
    kore_equals(phi0, phi1, phi2, phi3),
    Implies(
        kore_implies(phi1, phi4, phi2),
        kore_implies(phi1, phi4, phi3),
    ),
)
# (phi2:{phi0} k= phi2:{phi0}):{phi1}
eq_id_axiom = kore_equals(phi0, phi1, phi2, phi2)

# (phi2:{phi0} k= phi3:{phi0}):{phi1} -> ((phi3:{phi0} k= phi4:{phi0}):{phi1} -> (phi2:{phi0} k= phi4:{phi0}):{phi1})
eq_trans_axiom = Implies(
    kore_equals(phi0, phi1, phi2, phi3),
    Implies(kore_equals(phi0, phi1, phi3, phi4), kore_equals(phi0, phi1, phi2, phi4)),
)


# TODO: Add kore-transitivity
class KoreLemmas(ProofExp):
    def __init__(self) -> None:
        super().__init__(
            axioms=[
                keq_substitution_axiom,
                right_top_in_eq_axiom,
                reduce_equational_as_axiom,
                reduce_in_axiom,
                left_top_in_imp_axiom,
                remove_top_imp_right_axiom,
                reduce_top_axiom,
                keq_next_substitution_axiom,
                keq_implication_axiom,
                eq_id_axiom,
                eq_trans_axiom,
            ],
            notations=list(KORE_NOTATIONS),
        )
        self.definedness = self.import_module(Definedness())

    def equality_with_subst(self, phi: Pattern, equality: ProofThunk):
        """
                p1 k= p2
        ---------------------------
        phi[p1/x] k= phi[p2/x]
        """

        inner_sort, outer_sort, p1, p2 = kore_equals.assert_matches(equality.conc)
        return self.modus_ponens(
            self.dynamic_inst(
                self.load_axiom(keq_substitution_axiom), {0: inner_sort, 1: outer_sort, 2: p1, 3: p2, 4: phi}
            ),
            equality,
        )

    def reduce_equational_as(self, phi: ProofThunk):
        """
                (phi2 k⊆ (phi2 k⋀ phi2)) k-> phi3
        ---------------------------------------------------------
                phi3
        """
        _, requirement, conclusion = kore_implies.assert_matches(phi.conc)
        inner_sort, outer_sort, _, expression, _ = kore_equational_as.assert_matches(requirement)
        return self.modus_ponens(
            self.dynamic_inst(
                self.load_axiom(reduce_equational_as_axiom),
                {0: inner_sort, 1: outer_sort, 2: expression, 3: conclusion},
            ),
            phi,
        )

    def reduce_equational_in(self, phi: ProofThunk):
        """
                (phi2 k⊆ phi2) k-> phi3
        ---------------------------------------------------------
                phi3
        """
        _, requirement, conclusion = kore_implies.assert_matches(phi.conc)
        inner_sort, outer_sort, evar_plug, _ = kore_in.assert_matches(requirement)
        return self.modus_ponens(
            self.dynamic_inst(
                self.load_axiom(reduce_in_axiom),
                {0: inner_sort, 1: outer_sort, 2: evar_plug, 3: conclusion},
            ),
            phi,
        )

    def reduce_right_top_in_eq(self, phi: ProofThunk):
        """
                phi0 k= phi1 k⋀ k⊤
        ---------------------------
                phi0 k= phi1
        """
        inner_sort, outer_sort, left, right_conj = kore_equals.assert_matches(phi.conc)
        right, _ = kore_and.assert_matches(right_conj)
        return self.modus_ponens(
            self.dynamic_inst(
                self.load_axiom(right_top_in_eq_axiom),
                {0: inner_sort, 1: outer_sort, 2: left, 3: right},
            ),
            phi,
        )

    def reduce_right_top_in_imp(self, phi: ProofThunk):
        """
                phi1 k⋀ k⊤ k-> phi2
        ---------------------------
                phi1 k-> phi2
        """
        sort, left_conj, conclusion = kore_implies.assert_matches(phi.conc)
        left, _ = kore_and.assert_matches(left_conj)
        return self.modus_ponens(
            self.dynamic_inst(
                self.load_axiom(remove_top_imp_right_axiom),
                {0: sort, 1: left, 2: conclusion},
            ),
            phi,
        )

    def reduce_left_top_in_imp(self, phi: ProofThunk):
        """
                k⊤ k⋀ phi1 k-> phi2
        ---------------------------
                phi1 k-> phi2
        """
        sort, left_conj, conclusion = kore_implies.assert_matches(phi.conc)
        _, right = kore_and.assert_matches(left_conj)
        return self.modus_ponens(
            self.dynamic_inst(
                self.load_axiom(left_top_in_imp_axiom),
                {0: sort, 1: right, 2: conclusion},
            ),
            phi,
        )

    def reduce_top_in_imp(self, phi: ProofThunk):
        """
                k⊤ k-> phi1
        ---------------------------
                phi1
        """
        sort, _, conclusion = kore_implies.assert_matches(phi.conc)
        return self.modus_ponens(
            self.dynamic_inst(
                self.load_axiom(reduce_top_axiom),
                {0: sort, 1: conclusion},
            ),
            phi,
        )

    def subst_in_rewrite_target(self, equality: ProofThunk, imp: ProofThunk, phi1: Pattern):
        """
        p1 k= p2        phi0  k-> next(phi1[p1/x])
        ------------------------------------------
                phi0 k-> next(phi1[p2/x])
        """

        # Proof Outline:
        # 1. Axiom p1 k= p2 -> (next(phi0[p1/x])  k= next(phi0[p2/x]))
        # 2. Axiom p1 k= p2 -> ((psi k-> p1) -> (psi k-> p2))
        # 3. Function:
        #    (a) p1 k= p2         (b) phi0  k-> next phi1[p1/x]
        #    --------------------------------------------------
        #    (c) phi0  k-> next phi1[p2/x]

        # - MP on 1 and a, with subst p1 |-> p1, p2 |-> p2, phi0 |-> phi1
        #     ==(d)=>> next(phi1[p1/x])  k= next(phi1[p2/x])

        # - MP on 2 and d, with subst p1 |-> next(phi1[p1/x]), p2 |-> next(phi1[p2/x]), psi |-> phi0
        #     ==(e)=>> ((phi0 -> (next(phi1[p1/x])) k-> (phi0 -> next(phi1[p2/x]))))

        # - MP on e and b, with subst identity
        #     ==(f)=>> phi0 -> next(phi1[p2/x]))

        inner_sort, outer_sort, p1, p2 = kore_equals.assert_matches(equality.conc)
        imp_sort, phi0, imp_right = kore_implies.assert_matches(imp.conc)
        phi1_subst = kore_next.assert_matches(imp_right)[
            0
        ]  # assert_matched in this case returns a tuple, rather than an ESubst
        assert phi1.apply_esubst(HOLE.name, p1) == phi1_subst

        # MP on "Axiom p1 k= p2 -> (next(phi0[p1/x])  k= next(phi0[p2/x]))" and "p1 k= p2", with p1 |-> p1, p2 |-> p2, phi0 |-> phi1
        # conclude: next(phi1[p1/x])  k= next(phi1[p2/x])
        eq_next = self.modus_ponens(
            self.dynamic_inst(
                self.load_axiom(keq_next_substitution_axiom), {0: inner_sort, 1: outer_sort, 2: p1, 3: p2, 4: phi1}
            ),
            equality,
        )

        # MP on "Axiom: p1 k= p2 -> ((psi k-> p1) -> (psi k-> p2))" and "eq_next: next(phi1[p1/x])  k= next(phi1[p2/x])",
        #   with subst p1 |-> next(phi1[p1/x]), p2 |-> next(phi1[p2/x]), psi |-> phi0
        # conclude: ((phi0 k-> (next(phi1[p1/x])) -> (phi0 k-> next(phi1[p2/x]))))
        inner_sort, outer_sort, p1, p2 = kore_equals.assert_matches(eq_next.conc)
        phi0_imp_imp = self.modus_ponens(
            self.dynamic_inst(
                self.load_axiom(keq_implication_axiom),
                {0: inner_sort, 1: outer_sort, 2: p1, 3: p2, 4: phi0},
            ),
            eq_next,
        )

        # MP on "phi0_imp_imp: ((phi0 k-> (next(phi1[p1/x])) -> (phi0 k-> next(phi1[p2/x]))))" and "Premise: phi0  k-> next(phi1[p1/x])", with identity subst
        # conclude: phi0 k-> next(phi1[p2/x]))
        return self.modus_ponens(phi0_imp_imp, imp)

    def sorted_eq_id(self, sort: Pattern, phi: Pattern):
        """
        ---------------------------
                phi k= phi
        """
        return self.dynamic_inst(
            self.load_axiom(eq_id_axiom),
            {0: sort, 1: sort, 2: phi},
        )

    def sorted_eq_trans(self, eq_phi0_phi1: ProofThunk, eq_phi1_phi2: ProofThunk):
        """
        phi0 k= phi1   phi1 k= phi2
        ---------------------------
                phi0 k= phi2
        """
        sort1, sort2, phi0, phi1 = kore_equals.assert_matches(eq_phi0_phi1.conc)
        sort1, sort2, phi1_p, phi2 = kore_equals.assert_matches(eq_phi1_phi2.conc)
        assert phi1 == phi1_p

        return self.modus_ponens(
            self.modus_ponens(
                self.dynamic_inst(
                    self.load_axiom(eq_trans_axiom),
                    {0: sort1, 1: sort2, 2: phi0, 3: phi1, 4: phi2},
                ),
                eq_phi0_phi1,
            ),
            eq_phi1_phi2,
        )


if __name__ == '__main__':
    KoreLemmas().main(sys.argv)
