from __future__ import annotations

from typing import TYPE_CHECKING

import pytest
from frozendict import frozendict

from proof_generation.aml import (
    App,
    ESubst,
    EVar,
    Exists,
    Implies,
    Instantiate,
    MetaVar,
    Mu,
    SSubst,
    SVar,
    Symbol,
    bot,
    neg,
)

if TYPE_CHECKING:
    from proof_generation.aml import Pattern

phi0 = MetaVar(0)
phi1 = MetaVar(1)
phi2 = MetaVar(2)
sigma0 = Symbol('s0')
sigma1 = Symbol('s1')
sigma2 = Symbol('s2')


@pytest.mark.parametrize(
    'pattern, evar_id, plug, expected',
    [
        # Atomic cases
        [EVar(0), 0, sigma1, sigma1],
        [EVar(0), 0, EVar(2), EVar(2)],
        [EVar(0), 1, EVar(2), EVar(0)],
        [SVar(0), 0, sigma0, SVar(0)],
        [SVar(1), 0, EVar(0), SVar(1)],
        [sigma0, 0, sigma1, sigma0],
        # Distribute over subpatterns
        [Implies(EVar(7), sigma1), 7, sigma0, Implies(sigma0, sigma1)],
        [Implies(EVar(7), sigma1), 6, sigma0, Implies(EVar(7), sigma1)],
        [App(EVar(7), sigma1), 7, sigma0, App(sigma0, sigma1)],
        [App(EVar(7), sigma1), 6, sigma0, App(EVar(7), sigma1)],
        # Distribute over subpatterns unless evar_id = binder
        [Exists(1, EVar(1)), 1, sigma2, Exists(1, EVar(1))],
        [Exists(0, EVar(1)), 1, sigma2, Exists(0, sigma2)],
        [Mu(1, EVar(1)), 0, sigma2, Mu(1, EVar(1))],
        [Mu(1, EVar(1)), 1, sigma2, Mu(1, sigma2)],
        # Subst on metavar should wrap in constructor
        [phi0, 0, sigma1, ESubst(phi0, EVar(0), sigma1)],
        # Subst when evar_id is fresh should do nothing
        [MetaVar(0, e_fresh=(EVar(0), EVar(1))), 0, sigma1, MetaVar(0, e_fresh=(EVar(0), EVar(1)))],
        # Subst on substs should stack
        [
            ESubst(phi0, EVar(0), sigma1),
            # EVar(0) is fresh in ^^, so we can only apply ESubst on other EVar
            1,
            sigma2,
            ESubst(ESubst(phi0, EVar(0), sigma1), EVar(1), sigma2),
        ],
        [
            SSubst(phi0, SVar(0), sigma1),
            0,
            sigma2,
            ESubst(SSubst(phi0, SVar(0), sigma1), EVar(0), sigma2),
        ],
        # Instantiate/Notation
        [
            Instantiate(App(phi0, phi1), frozendict({0: phi2, 1: phi1})),
            0,
            sigma1,
            Instantiate(
                App(phi0, phi1), frozendict({0: ESubst(phi2, EVar(0), sigma1), 1: ESubst(phi1, EVar(0), sigma1)})
            ),
        ],
    ],
)
def test_apply_esubst(pattern: Pattern, evar_id: int, plug: Pattern, expected: Pattern) -> None:
    actual = pattern.apply_esubst(evar_id, plug)
    assert actual == expected
    # TODO: Equality checks are modulo instantiation.
    # I feel this is a bit dangerous. We should instead have a separate `Pattern.equals_modulo` operation.
    assert type(actual) == type(expected)


@pytest.mark.parametrize(
    'pattern, svar_id, plug, expected',
    [
        # Atomic cases
        [EVar(0), 0, sigma1, EVar(0)],
        [EVar(0), 1, EVar(2), EVar(0)],
        [SVar(0), 0, sigma0, sigma0],
        [SVar(1), 0, EVar(0), SVar(1)],
        [sigma0, 0, sigma1, sigma0],
        # Distribute over subpatterns
        [Implies(SVar(7), sigma1), 7, sigma0, Implies(sigma0, sigma1)],
        [Implies(SVar(7), sigma1), 6, sigma0, Implies(SVar(7), sigma1)],
        [App(SVar(7), sigma1), 7, sigma0, App(sigma0, sigma1)],
        [App(SVar(7), sigma1), 6, sigma0, App(SVar(7), sigma1)],
        # Distribute over subpatterns unless svar_id = binder
        [Exists(1, SVar(0)), 0, sigma2, Exists(1, sigma2)],
        [Exists(1, sigma1), 1, sigma2, Exists(1, sigma1)],
        [Mu(1, SVar(1)), 0, sigma2, Mu(1, SVar(1))],
        [Mu(1, SVar(1)), 1, sigma2, Mu(1, SVar(1))],
        [Mu(1, SVar(2)), 2, sigma2, Mu(1, sigma2)],
        # Subst on metavar should wrap in constructor
        [phi0, 0, sigma1, SSubst(phi0, SVar(0), sigma1)],
        # Subst when evar_id is fresh should do nothing
        [MetaVar(0, s_fresh=(SVar(0), SVar(1))), 0, sigma1, MetaVar(0, s_fresh=(SVar(0), SVar(1)))],
        # Subst on substs should stack
        [
            ESubst(phi0, EVar(0), sigma1),
            0,
            sigma1,
            SSubst(ESubst(phi0, EVar(0), sigma1), SVar(0), sigma1),
        ],
        [
            SSubst(phi0, SVar(0), sigma1),
            0,
            sigma1,
            SSubst(SSubst(phi0, SVar(0), sigma1), SVar(0), sigma1),
        ],
        # Instantiate/Notation
        pytest.param(
            Instantiate(App(phi0, phi1), frozendict({0: phi2, 1: phi1})),
            0,
            sigma1,
            Instantiate(
                App(phi0, phi1), frozendict({0: SSubst(phi2, SVar(0), sigma1), 1: SSubst(phi1, SVar(0), sigma1)})
            ),
            marks=[pytest.mark.xfail],
        ),
    ],
)
def test_apply_ssubst(pattern: Pattern, svar_id: int, plug: Pattern, expected: Pattern) -> None:
    actual = pattern.apply_ssubst(svar_id, plug)
    assert actual == expected
    assert type(actual) == type(expected)


@pytest.mark.parametrize(
    'pattern, plugs, expected',
    [
        # Atomic cases
        [EVar(0), {0: sigma1}, sigma1],
        [EVar(0), {0: EVar(2)}, EVar(2)],
        [EVar(0), {1: EVar(2)}, EVar(0)],
        [Instantiate(EVar(0), frozendict()), {0: sigma0}, sigma0],
        # Notation (Instantiate with no free E/SVars) is being preserved
        [
            Instantiate(Implies(phi0, bot()), frozendict({0: EVar(0)})),
            {0: sigma0},
            Instantiate(Implies(phi0, bot()), frozendict({0: sigma0})),
        ],
        [
            Instantiate(Implies(neg(phi0), phi1), frozendict({0: EVar(0)})),
            {0: sigma0},
            Instantiate(Implies(neg(phi0), phi1), frozendict({0: sigma0, 1: ESubst(phi1, EVar(0), sigma0)})),
        ],
        # Several plugs
        [Implies(EVar(0), EVar(1)), {0: sigma0}, Implies(sigma0, EVar(1))],
        [Implies(EVar(0), EVar(1)), {0: sigma0, 1: sigma1}, Implies(sigma0, sigma1)],
    ],
)
def test_apply_esubsts(pattern: Pattern, plugs: dict[int, Pattern], expected: Pattern) -> None:
    assert pattern.apply_esubsts(plugs) == expected


def test_metavars() -> None:
    assert phi0.metavars() == {phi0}
    assert Implies(phi0, phi1).metavars() == {phi0, phi1}
    assert App(phi0, phi1).metavars() == {phi0, phi1}
    assert Exists(0, phi1).metavars() == {phi1}
    assert Mu(0, phi1).metavars() == {phi1}
    assert Instantiate(phi0, frozendict({0: phi1})).metavars() == {phi1}
    assert Instantiate(phi0, frozendict({1: phi1})).metavars() == {phi0}

    assert ESubst(phi1, EVar(0), phi0).metavars() == {phi1, phi0}
    assert SSubst(phi1, SVar(0), phi0).metavars() == {phi1, phi0}

    assert ESubst(MetaVar(1), EVar(0), phi0).metavars() == {phi0, phi1}

    assert SSubst(MetaVar(1), SVar(0), phi0).metavars() == {phi0, phi1}


# Subst 0 for 1 and then 1 for 2
ssubst_stack_seq = lambda term: SSubst(SSubst(term, SVar(0), plug=SVar(1)), SVar(1), plug=SVar(2))

# Subst 1 for 2 and then 0 for 1
ssubst_stack_seq_rev = lambda term: SSubst(SSubst(pattern=term, var=SVar(1), plug=SVar(2)), var=SVar(0), plug=SVar(1))

# Subst 0 for 1 and then 1 for 2
esubst_stack_seq = lambda term: ESubst(ESubst(term, EVar(0), plug=EVar(1)), EVar(1), plug=EVar(2))

# Subst 1 for 2 and then 0 for 1
esubst_stack_seq_rev = lambda term: ESubst(ESubst(pattern=term, var=EVar(1), plug=EVar(2)), var=EVar(0), plug=EVar(1))

# Subst SVar1 for Evar1 and then EVar1 for EVar2
stack_mixed1 = lambda term: ESubst(SSubst(pattern=term, var=SVar(1), plug=EVar(1)), var=EVar(1), plug=EVar(2))


@pytest.mark.parametrize(
    'pattern, plugs, expected',
    [
        [esubst_stack_seq(phi0), {0: EVar(0)}, EVar(2)],
        [esubst_stack_seq(phi0), {0: EVar(1)}, EVar(2)],
        [esubst_stack_seq(phi1), {0: EVar(1)}, esubst_stack_seq(phi1)],
        [esubst_stack_seq(phi0), {0: phi1}, esubst_stack_seq(phi1)],
        [esubst_stack_seq_rev(phi0), {0: EVar(0)}, EVar(1)],
        [esubst_stack_seq_rev(phi0), {0: phi1}, esubst_stack_seq_rev(phi1)],
        [stack_mixed1(phi0), {0: SVar(1)}, EVar(2)],
        [stack_mixed1(phi0), {0: SVar(2)}, SVar(2)],
        [ssubst_stack_seq(phi0), {0: SVar(0)}, SVar(2)],
        [ssubst_stack_seq(phi0), {0: SVar(1)}, SVar(2)],
        [ssubst_stack_seq(phi1), {0: SVar(1)}, ssubst_stack_seq(phi1)],
        [ssubst_stack_seq(phi0), {0: phi1}, ssubst_stack_seq(phi1)],
        [ssubst_stack_seq_rev(phi0), {0: SVar(0)}, SVar(1)],
        [ssubst_stack_seq_rev(phi0), {0: phi1}, ssubst_stack_seq_rev(phi1)],
        [stack_mixed1(phi0), {0: SVar(1)}, EVar(2)],
        [stack_mixed1(phi0), {0: SVar(2)}, SVar(2)],
        # This fails if metavar instantiations are not propagated into the plug
        [SSubst(phi0, SVar(0), phi0), {0: SVar(0)}, SVar(0)],
        [Instantiate(phi0, frozendict({0: phi1})), {1: sigma1}, sigma1],
        [Instantiate(phi0, frozendict({0: phi0})), {0: sigma1}, sigma1],
        [Instantiate(phi0, frozendict({0: phi1})), {0: sigma1}, Instantiate(phi0, frozendict({0: phi1}))],
    ],
)
def test_instantiate_subst(pattern: Pattern, plugs: dict[int, Pattern], expected: Pattern) -> None:
    assert pattern.instantiate(plugs) == expected


@pytest.mark.parametrize(
    'pattern, expected',
    [
        # Atomic cases
        [EVar(0), {EVar(0)}],
        [SVar(0), {SVar(0)}],
        [Symbol('0'), set()],
        [MetaVar(0), set()],
        # More complicated
        [Implies(EVar(0), SVar(1)), {EVar(0), SVar(1)}],
        [Exists(0, Implies(EVar(0), SVar(0))), {SVar(0)}],
        [Mu(0, Implies(EVar(0), SVar(0))), {EVar(0)}],
        # Substs need to plug in at least one instance
        [ESubst(MetaVar(0), EVar(0), EVar(1)), {EVar(1)}],
        [SSubst(MetaVar(0), SVar(0), EVar(1)), {EVar(1)}],
        [SSubst(MetaVar(0), SVar(0), Symbol('1')), set()],
        # Instantiate
        [Instantiate(MetaVar(0), frozendict({0: EVar(0)})), {EVar(0)}],
        [Instantiate(ESubst(MetaVar(0), EVar(0), EVar(1)), frozendict({0: EVar(0)})), {EVar(1)}],
    ],
)
def test_occurring_vars(pattern: Pattern, expected: set[EVar | SVar]) -> None:
    assert pattern.occurring_vars() == expected
