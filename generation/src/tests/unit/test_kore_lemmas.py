from frozendict import frozendict

from proof_generation.pattern import App, Instantiate, MetaVar, Notation, Symbol
from proof_generation.proofs.kore_lemmas import deconstruct_nary_application, nary_app, nary_cell

phi0 = MetaVar(0)
phi1 = MetaVar(1)
phi2 = MetaVar(2)

foo_symbol = Symbol('foo')
foo_app = nary_app(foo_symbol, 3)
foo_cell = nary_cell(foo_symbol, 3)

bar_symbol = Symbol('bar')
bar = Notation('bar', bar_symbol, 'bar')


def test_nary_application() -> None:
    expected = Instantiate(App(App(App(foo_symbol, phi0), phi1), phi2), frozendict({0: bar(), 1: bar(), 2: bar()}))
    assert foo_app(bar(), bar(), bar()) == expected
    assert foo_cell(bar(), bar(), bar()) == expected


def test_deconstruct_nary_application() -> None:
    assert deconstruct_nary_application(foo_symbol) == (foo_symbol, ())
    assert deconstruct_nary_application(App(foo_symbol, bar())) == (foo_symbol, (bar(),))
    assert deconstruct_nary_application(App(foo_symbol, App(bar(), bar()))) == (foo_symbol, (App(bar(), bar()),))
    assert deconstruct_nary_application(App(App(foo_symbol, bar()), bar())) == (foo_symbol, (bar(), bar()))

    assert deconstruct_nary_application(foo_app.definition) == (foo_symbol, (phi0, phi1, phi2))
    assert deconstruct_nary_application(foo_cell.definition) == (foo_symbol, (phi0, phi1, phi2))
