from __future__ import annotations

from frozendict import frozendict

from proof_generation.aml import App, EVar, Exists, Implies, Instantiate, Mu, Notation, SVar, match, match_single
from proof_generation.proofs.propositional import Propositional, _and, _or, bot, neg, phi0, phi1, phi2, top


def test_match() -> None:
    assert match_single(phi0, phi0) == {0: phi0}
    assert match_single(phi0, phi1) == {0: phi1}
    assert match_single(phi0, Implies(phi0, phi1)) == {0: Implies(phi0, phi1)}
    # The following fails because the provided substitution conflicts with the
    # one induced by the input patterns
    assert match_single(phi0, phi0, extend={0: phi2}) == None

    assert match_single(Implies(phi0, phi1), phi0) == None
    assert match_single(Implies(phi0, phi1), App(phi1, phi2)) == None
    assert match_single(Implies(phi0, phi1), Implies(phi1, phi2)) == {0: phi1, 1: phi2}
    assert match_single(Implies(phi0, phi0), Implies(phi1, phi2)) == None
    assert match_single(Implies(phi0, phi2), Implies(phi1, phi2)) == {0: phi1, 2: phi2}
    assert match_single(Implies(EVar(0), phi0), Implies(EVar(1), phi2)) == None
    assert match_single(Implies(phi0, EVar(2)), Implies(phi1, EVar(1))) == None

    assert match_single(App(phi0, phi1), phi0) == None
    assert match_single(App(phi0, phi1), Implies(phi1, phi2)) == None
    assert match_single(App(phi0, phi1), App(phi1, phi2)) == {0: phi1, 1: phi2}
    assert match_single(App(phi0, phi0), App(phi1, phi2)) == None
    # The 2 -> phi2 is required because the metavars might have different constrains
    assert match_single(App(phi0, phi2), App(phi1, phi2)) == {0: phi1, 2: phi2}
    assert match_single(App(EVar(0), phi0), App(EVar(1), phi2)) == None
    assert match_single(App(phi0, EVar(2)), App(phi1, EVar(1))) == None

    assert match_single(SVar(0), App(phi1, phi2)) == None
    assert match_single(SVar(0), SVar(1)) == None
    assert match_single(SVar(0), EVar(0)) == None
    assert match_single(SVar(0), SVar(0)) == {}

    assert match_single(EVar(0), App(phi1, phi2)) == None
    assert match_single(EVar(0), EVar(1)) == None
    assert match_single(EVar(0), SVar(0)) == None
    assert match_single(EVar(0), EVar(0)) == {}

    assert match_single(Mu(0, phi1), App(phi1, phi2)) == None
    assert match_single(Mu(0, phi1), Mu(1, phi1)) == None
    assert match_single(Mu(0, phi1), Mu(0, phi0)) == {1: phi0}

    assert match_single(Exists(0, phi1), Mu(1, phi2)) == None
    assert match_single(Exists(0, phi1), Exists(1, phi1)) == None
    assert match_single(Exists(0, phi1), Exists(0, phi0)) == {1: phi0}

    assert match_single(bot(), bot()) == {}
    assert match_single(bot(), bot.definition) == {}
    assert match_single(_and.definition, _and(Mu(0, phi1), Mu(0, phi0))) == {0: Mu(0, phi1), 1: Mu(0, phi0)}
    assert match_single(_and.definition, _and.definition) == {0: phi0, 1: phi1}
    assert match_single(_or.definition, _and.definition) == None
    assert match_single(_or.definition, Implies(Implies(phi1, bot()), EVar(1))) == {0: phi1, 1: EVar(1)}

    foo = Notation('foo', 3, phi0, '{0}')
    assert foo.matches(phi1) == (phi1, phi1, phi2)

    assert match([(Implies(phi0, phi1), Implies(phi0, phi0)), (Implies(phi1, phi2), Implies(phi0, phi0))]) == {
        0: phi0,
        1: phi0,
        2: phi0,
    }
    assert match([(Implies(phi0, phi1), Implies(phi2, SVar(0))), (Implies(phi1, phi2), Implies(SVar(0), phi0))]) == {
        0: phi2,
        1: SVar(0),
        2: phi0,
    }
    assert match([(Implies(phi0, phi1), Implies(phi0, SVar(0))), (Implies(phi1, phi2), Implies(phi0, phi0))]) == None


def test_pretty_diff() -> None:
    exp = Propositional()
    assert exp.pretty_diff(_or(phi0, phi1), _or(phi0, phi1)) == '(phi0 ⋁ phi1)'
    assert exp.pretty_diff(_or(phi0, phi1), _or(phi0, phi1).simplify()) == '(phi0 ⋁ phi1)'
    # fmt: off

    # App
    assert exp.pretty_diff(App(phi0, phi1), App(phi0, phi1)) == '(phi0 · phi1)'
    assert exp.pretty_diff(App(phi0, phi1), App(phi1, phi2)) == \
        ('(\n'
        '--- phi0\n'
        '+++ phi1\n'
        ' · \n'
        '--- phi1\n'
        '+++ phi2\n'
        ')')

    # Implies
    assert exp.pretty_diff(Implies(phi0, phi1), Implies(phi0, phi1)) == '(phi0 -> phi1)'
    assert exp.pretty_diff(Implies(phi0, phi1), Implies(phi1, phi2)) == \
        ('(\n'
        '--- phi0\n'
        '+++ phi1\n'
        ' -> \n'
        '--- phi1\n'
        '+++ phi2\n'
        ')')

    # Exists
    assert exp.pretty_diff(Exists(0, phi1), Exists(0, phi1)) == '(∃ x0 . phi1)'
    assert exp.pretty_diff(Exists(0, phi1), Exists(1, phi1)) == '\n--- (∃ x0 . phi1)\n+++ (∃ x1 . phi1)\n'
    assert exp.pretty_diff(Exists(0, phi1), Exists(0, phi2)) == \
        ('(∃ x0 . \n'
        '--- phi1\n'
        '+++ phi2\n'
        ')')

    # Diff preserves notation
    assert exp.pretty_diff(_or(phi0, phi1), _or(phi1, phi2)) == \
        ('(\n'
        '--- phi0\n'
        '+++ phi1\n'
        ' ⋁ \n'
        '--- phi1\n'
        '+++ phi2\n'
        ')')

    # Diff preserves notation left only
    assert exp.pretty_diff(_or(phi0, phi1), _or(phi1, phi2).simplify()) == \
        ('(\n'
        '--- phi0\n'
        '+++ phi1\n'
        ' ⋁ \n'
        '--- phi1\n'
        '+++ phi2\n'
        ')')
    # Diff preserves notation right only
    assert exp.pretty_diff(_or(phi0, phi1).simplify(), _or(phi1, phi2)) == \
        ('(\n'
        '--- phi0\n'
        '+++ phi1\n'
        ' ⋁ \n'
        '--- phi1\n'
        '+++ phi2\n'
        ')')

    # Different notations. Depends on the order.
    assert exp.pretty_diff(top(), neg(bot())) == '⊤'
    assert exp.pretty_diff(neg(bot()), top()) == '¬⊥'

    # Incomplete instantiations
    assert exp.pretty_diff(Instantiate(_or.definition, frozendict({0: phi2})),
                           Instantiate(_or.definition, frozendict({2: phi0}))
                          ) == \
        ('((phi0 -> (μ X0 . X0)[])[0: phi0] -> phi1)[0: \n'
        '--- phi2\n'
        '+++ phi0\n'
        ', 2: \n'
        '--- phi2\n'
        '+++ phi0\n'
        ']')

    # fmt: on
