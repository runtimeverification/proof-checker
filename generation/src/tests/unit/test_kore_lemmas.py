from frozendict import frozendict

from proof_generation.aml import App, Instantiate, MetaVar, Notation, PrettyOptions, Symbol
from proof_generation.interpreter import BasicInterpreter, ExecutionPhase
from proof_generation.proofs.kore import (
    KoreLemmas,
    deconstruct_nary_application,
    kore_and,
    kore_equals,
    kore_equational_as,
    kore_implies,
    kore_in,
    kore_next,
    kore_top,
    nary_app,
)
from proof_generation.proofs.substitution import HOLE
from tests.unit.test_propositional import make_pt

phi0 = MetaVar(0)
phi1 = MetaVar(1)
phi2 = MetaVar(2)

foo_symbol = Symbol('foo')
foo_app = nary_app(foo_symbol, 3)
foo_cell = nary_app(foo_symbol, 3, True)

bar_symbol = Symbol('bar')
bar = Notation('bar', 0, bar_symbol, 'bar')


def test_nary_application() -> None:
    expected = Instantiate(App(App(App(foo_symbol, phi0), phi1), phi2), frozendict({0: bar(), 1: bar(), 2: bar()}))
    assert foo_app(bar(), bar(), bar()) == expected
    assert foo_cell(bar(), bar(), bar()) == expected


def test_print_nary_application() -> None:
    pretty_options = PrettyOptions(notations={foo_app.definition: foo_app, bar.definition: bar})
    assert foo_app(bar(), bar(), bar()).pretty(pretty_options) == 'foo(bar, bar, bar)'
    pretty_options = PrettyOptions(notations={foo_cell.definition: foo_cell, bar.definition: bar})
    assert foo_cell(bar(), bar(), bar()).pretty(pretty_options) == '<foo> bar bar bar </foo>'


def test_deconstruct_nary_application() -> None:
    assert deconstruct_nary_application(foo_symbol) == (foo_symbol, ())
    assert deconstruct_nary_application(App(foo_symbol, bar())) == (foo_symbol, (bar(),))
    assert deconstruct_nary_application(App(foo_symbol, App(bar(), bar()))) == (foo_symbol, (App(bar(), bar()),))
    assert deconstruct_nary_application(App(App(foo_symbol, bar()), bar())) == (foo_symbol, (bar(), bar()))

    assert deconstruct_nary_application(foo_app.definition) == (foo_symbol, (phi0, phi1, phi2))
    assert deconstruct_nary_application(foo_cell.definition) == (foo_symbol, (phi0, phi1, phi2))


def test_equality_with_subst() -> None:
    theory = KoreLemmas()

    sort1 = Symbol('sort1')
    sort2 = Symbol('sort2')
    value_a = Symbol('value_a')
    value_b = Symbol('value_b')
    value_c = Symbol('value_c')
    phi = App(value_c, HOLE)

    # Test simple case
    thunk = make_pt(kore_equals(sort1, sort2, value_a, value_b))
    proof = theory.equality_with_subst(phi, thunk)
    expected = kore_equals(sort1, sort2, phi.apply_esubst(HOLE.name, value_a), phi.apply_esubst(HOLE.name, value_b))
    assert proof(BasicInterpreter(phase=ExecutionPhase.Proof)).conclusion == expected


def test_reduce_equational_as() -> None:
    theory = KoreLemmas()

    sort1 = Symbol('sort1')
    sort2 = Symbol('sort2')
    value_a = Symbol('value_a')
    conclusion = App(Symbol('x'), Symbol('y'))

    test_expression = kore_implies(sort2, kore_equational_as(sort1, sort2, value_a, value_a, value_a), conclusion)
    thunk = make_pt(test_expression)
    proof = theory.reduce_equational_as(thunk)
    expected = conclusion
    assert proof(BasicInterpreter(phase=ExecutionPhase.Proof)).conclusion == expected


def test_reduce_equational_in() -> None:
    theory = KoreLemmas()

    sort1 = Symbol('sort1')
    sort2 = Symbol('sort2')
    value_a = Symbol('value_a')
    conclusion = App(Symbol('x'), Symbol('y'))

    test_expression = kore_implies(sort2, kore_in(sort1, sort2, value_a, value_a), conclusion)
    thunk = make_pt(test_expression)
    proof = theory.reduce_equational_in(thunk)
    expected = conclusion
    assert proof(BasicInterpreter(phase=ExecutionPhase.Proof)).conclusion == expected


def test_reduce_right_top_eq_conjunct() -> None:
    theory = KoreLemmas()

    sort1 = Symbol('sort1')
    sort2 = Symbol('sort2')
    value_a = Symbol('value_a')
    value_b = Symbol('value_b')
    ktop = kore_top(sort1)

    test_expression = kore_equals(sort1, sort2, value_a, kore_and(value_b, ktop))
    thunk = make_pt(test_expression)
    proof = theory.reduce_right_top_in_eq(thunk)
    expected = kore_equals(sort1, sort2, value_a, value_b)
    assert proof(BasicInterpreter(phase=ExecutionPhase.Proof)).conclusion == expected


def test_reduce_left_top_imp_conjunct() -> None:
    theory = KoreLemmas()

    sort1 = Symbol('sort1')
    value_a = Symbol('value_a')
    value_b = Symbol('value_b')
    ktop = kore_top(sort1)

    test_expression = kore_implies(sort1, kore_and(ktop, value_a), value_b)
    thunk = make_pt(test_expression)
    proof = theory.reduce_left_top_in_imp(thunk)
    expected = kore_implies(sort1, value_a, value_b)
    assert proof(BasicInterpreter(phase=ExecutionPhase.Proof)).conclusion == expected


def test_reduce_right_top_imp_conjunct() -> None:
    theory = KoreLemmas()

    sort1 = Symbol('sort1')
    value_a = Symbol('value_a')
    value_b = Symbol('value_b')
    ktop = kore_top(sort1)

    test_expression = kore_implies(sort1, kore_and(value_a, ktop), value_b)
    thunk = make_pt(test_expression)
    proof = theory.reduce_right_top_in_imp(thunk)
    expected = kore_implies(sort1, value_a, value_b)
    assert proof(BasicInterpreter(phase=ExecutionPhase.Proof)).conclusion == expected


def test_reduce_top_imp() -> None:
    theory = KoreLemmas()

    sort1 = Symbol('sort1')
    value_a = Symbol('value_a')
    ktop = kore_top(sort1)

    test_expression = kore_implies(sort1, ktop, value_a)
    thunk = make_pt(test_expression)
    proof = theory.reduce_top_in_imp(thunk)
    expected = value_a
    assert proof(BasicInterpreter(phase=ExecutionPhase.Proof)).conclusion == expected


def test_subst_in_rewrite_target() -> None:
    theory = KoreLemmas()

    # Premise 1: p1 k= p2
    inner_sort = Symbol('inner_sort')
    outer_sort = Symbol('outer_sort')
    p1 = Symbol('p1')
    p2 = Symbol('p2')
    premise1 = kore_equals(inner_sort, outer_sort, p1, p2)

    # Premise 2: phi0  k-> next(phi1[p1/x])
    phi0 = Symbol('phi0')
    phi1 = MetaVar(0, app_ctx_holes=(HOLE,))
    premise2 = kore_implies(outer_sort, phi0, kore_next(phi1.apply_esubst(0, p1)))

    thunk1 = make_pt(premise1)
    thunk2 = make_pt(premise2)
    proof = theory.subst_in_rewrite_target(thunk1, thunk2, phi1)

    # Expected conclusion: phi0 k-> next(phi1[p2/x])
    expected = kore_implies(outer_sort, phi0, kore_next(phi1.apply_esubst(0, p2)))
    assert proof(BasicInterpreter(phase=ExecutionPhase.Proof)).conclusion == expected


def test_sorted_eq_id() -> None:
    theory = KoreLemmas()

    sort1 = Symbol('sort')
    value_a = Symbol('value_a')

    proof = theory.sorted_eq_id(sort1, sort1, value_a)
    expected = kore_equals(sort1, sort1, value_a, value_a)
    assert proof(BasicInterpreter(phase=ExecutionPhase.Proof)).conclusion == expected


def test_sorted_eq_trans() -> None:
    theory = KoreLemmas()

    sort1 = Symbol('sort')
    value_a = Symbol('value_a')
    value_b = Symbol('value_b')
    value_c = Symbol('value_c')

    eq_a_b = make_pt(kore_equals(sort1, sort1, value_a, value_b))
    eq_b_c = make_pt(kore_equals(sort1, sort1, value_b, value_c))
    proof = theory.sorted_eq_trans(eq_a_b, eq_b_c)
    expected = kore_equals(sort1, sort1, value_a, value_c)
    assert proof(BasicInterpreter(phase=ExecutionPhase.Proof)).conclusion == expected
