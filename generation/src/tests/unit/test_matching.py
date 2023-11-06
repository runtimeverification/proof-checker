from __future__ import annotations

from proof_generation.pattern import App, EVar, Exists, Implies, Mu, SVar, match, match_single
from proof_generation.proofs.propositional import And, Or, bot, phi0, phi1, phi2


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

    assert match_single(bot, bot) == {}
    assert match_single(bot, bot.definition()) == {}
    assert match_single(And(phi0, phi1), And(Mu(0, phi1), Mu(0, phi0))) == {0: Mu(0, phi1), 1: Mu(0, phi0)}
    assert match_single(And(phi0, phi1), And.definition()) == {0: phi0, 1: phi1}
    assert match_single(Or(phi0, phi1), And.definition()) == None
    assert match_single(Or(phi0, phi1), Implies(Implies(phi1, bot), EVar(1))) == {0: phi1, 1: EVar(1)}

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
