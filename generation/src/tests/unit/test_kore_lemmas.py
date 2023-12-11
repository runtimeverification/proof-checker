from frozendict import frozendict

from proof_generation.basic_interpreter import BasicInterpreter, ExecutionPhase
from proof_generation.pattern import App, EVar, Instantiate, MetaVar, Notation, PrettyOptions, Symbol
from proof_generation.proofs.kore import KoreLemmas, deconstruct_nary_application, kore_equals, nary_app
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
    phi = App(value_c, EVar(0))

    # Test simple case
    thunk = make_pt(kore_equals(sort1, sort2, value_a, value_b))
    proof = theory.equality_with_subst(phi, thunk)
    expected = kore_equals(sort1, sort2, phi.apply_esubst(0, value_a), phi.apply_esubst(0, value_b))
    assert proof(BasicInterpreter(phase=ExecutionPhase.Proof)).conclusion == expected
