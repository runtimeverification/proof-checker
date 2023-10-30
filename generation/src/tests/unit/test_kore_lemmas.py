from proof_generation.pattern import App, Symbol
from proof_generation.proofs.kore_lemmas import deconstruct_nary_application


def test_deconstruct_nary_application() -> None:
    s0 = Symbol('foo')
    s1 = Symbol('bar')
    assert deconstruct_nary_application(s0) == (s0, ())
    assert deconstruct_nary_application(App(s0, s1)) == (s0, (s1,))
    assert deconstruct_nary_application(App(s0, App(s1, s1))) == (s0, (App(s1, s1),))
    assert deconstruct_nary_application(App(App(s0, s1), s1)) == (s0, (s1, s1))
