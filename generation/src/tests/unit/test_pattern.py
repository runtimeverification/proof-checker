from __future__ import annotations

from typing import TYPE_CHECKING

import pytest

from proof_generation.pattern import App, ESubst, EVar, Exists, Implies, MetaVar, Mu, SSubst, SVar, Symbol

if TYPE_CHECKING:
    from collections.abc import Callable

    from proof_generation.pattern import Pattern


@pytest.mark.parametrize(
    'pattern, evar_id, plug, expected',
    [
        # Atomic cases
        [EVar(0), 0, Symbol('s1'), Symbol('s1')],
        [EVar(0), 0, EVar(2), EVar(2)],
        [EVar(0), 1, EVar(2), EVar(0)],
        [SVar(0), 0, Symbol('s0'), SVar(0)],
        [SVar(1), 0, EVar(0), SVar(1)],
        [Symbol('s0'), 0, Symbol('s1'), Symbol('s0')],
        # Distribute over subpatterns
        [Implies(EVar(7), Symbol('s1')), 7, Symbol('s0'), Implies(Symbol('s0'), Symbol('s1'))],
        [Implies(EVar(7), Symbol('s1')), 6, Symbol('s0'), Implies(EVar(7), Symbol('s1'))],
        [App(EVar(7), Symbol('s1')), 7, Symbol('s0'), App(Symbol('s0'), Symbol('s1'))],
        [App(EVar(7), Symbol('s1')), 6, Symbol('s0'), App(EVar(7), Symbol('s1'))],
        # Distribute over subpatterns unless evar_id = binder
        [Exists(1, EVar(1)), 1, Symbol('s2'), Exists(1, EVar(1))],
        [Exists(0, EVar(1)), 1, Symbol('s2'), Exists(0, Symbol('s2'))],
        [Mu(1, EVar(1)), 0, Symbol('s2'), Mu(1, EVar(1))],
        [Mu(1, EVar(1)), 1, Symbol('s2'), Mu(1, Symbol('s2'))],
        # Subst on metavar should wrap in constructor
        [MetaVar(0), 0, Symbol('s1'), ESubst(MetaVar(0), EVar(0), Symbol('s1'))],
        # Subst when evar_id is fresh should do nothing
        [MetaVar(0, e_fresh=(EVar(0), EVar(1))), 0, Symbol('s1'), MetaVar(0, e_fresh=(EVar(0), EVar(1)))],
        # Subst on substs should stack
        [
            ESubst(MetaVar(0), EVar(0), Symbol('s1')),
            0,
            Symbol('s1'),
            ESubst(ESubst(MetaVar(0), EVar(0), Symbol('s1')), EVar(0), Symbol('s1')),
        ],
        [
            SSubst(MetaVar(0), SVar(0), Symbol('s1')),
            0,
            Symbol('s1'),
            ESubst(SSubst(MetaVar(0), SVar(0), Symbol('s1')), EVar(0), Symbol('s1')),
        ],
    ],
)
def test_apply_esubst(pattern: Pattern, evar_id: int, plug: Pattern, expected: Pattern) -> None:
    assert pattern.apply_esubst(evar_id, plug) == expected


# Subst 0 for 1 and then 1 for 2
esubst_stack_seq = lambda term: ESubst(ESubst(term, EVar(0), plug=EVar(1)), EVar(1), plug=EVar(2))

# Subst 1 for 2 and then 0 for 1
esubst_stack_seq_rev = lambda term: ESubst(ESubst(pattern=term, var=EVar(1), plug=EVar(2)), var=EVar(0), plug=EVar(1))

# Subst SVar1 for Evar1 and then EVar1 for EVar2
stack_mixed1 = lambda term: ESubst(SSubst(pattern=term, var=SVar(1), plug=EVar(1)), var=EVar(1), plug=EVar(2))


@pytest.mark.parametrize(
    'stack, mvar, plugs, expected',
    [
        [esubst_stack_seq, MetaVar(0), {0: EVar(0)}, EVar(2)],
        [esubst_stack_seq, MetaVar(0), {0: EVar(1)}, EVar(2)],
        [esubst_stack_seq, MetaVar(1), {0: EVar(1)}, esubst_stack_seq(MetaVar(1))],
        [esubst_stack_seq, MetaVar(0), {0: MetaVar(1)}, esubst_stack_seq(MetaVar(1))],
        [esubst_stack_seq_rev, MetaVar(0), {0: EVar(0)}, EVar(1)],
        [esubst_stack_seq_rev, MetaVar(0), {0: MetaVar(1)}, esubst_stack_seq_rev(MetaVar(1))],
        [stack_mixed1, MetaVar(0), {0: SVar(1)}, EVar(2)],
        [stack_mixed1, MetaVar(0), {0: SVar(2)}, SVar(2)],
    ],
)
def test_instantiate_esubst(
    stack: Callable[[MetaVar], Pattern], mvar: MetaVar, plugs: dict[int, Pattern], expected: Pattern
) -> None:
    assert stack(mvar).instantiate(plugs) == expected


@pytest.mark.parametrize(
    'pattern, svar_id, plug, expected',
    [
        # Atomic cases
        [EVar(0), 0, Symbol('s1'), EVar(0)],
        [EVar(0), 1, EVar(2), EVar(0)],
        [SVar(0), 0, Symbol('s0'), Symbol('s0')],
        [SVar(1), 0, EVar(0), SVar(1)],
        [Symbol('s0'), 0, Symbol('s1'), Symbol('s0')],
        # Distribute over subpatterns
        [Implies(SVar(7), Symbol('s1')), 7, Symbol('s0'), Implies(Symbol('s0'), Symbol('s1'))],
        [Implies(SVar(7), Symbol('s1')), 6, Symbol('s0'), Implies(SVar(7), Symbol('s1'))],
        [App(SVar(7), Symbol('s1')), 7, Symbol('s0'), App(Symbol('s0'), Symbol('s1'))],
        [App(SVar(7), Symbol('s1')), 6, Symbol('s0'), App(SVar(7), Symbol('s1'))],
        # Distribute over subpatterns unless svar_id = binder
        [Exists(1, SVar(0)), 0, Symbol('s2'), Exists(1, Symbol('s2'))],
        [Exists(1, Symbol('s1')), 1, Symbol('s2'), Exists(1, Symbol('s1'))],
        [Mu(1, SVar(1)), 0, Symbol('s2'), Mu(1, SVar(1))],
        [Mu(1, SVar(1)), 1, Symbol('s2'), Mu(1, SVar(1))],
        [Mu(1, SVar(2)), 2, Symbol('s2'), Mu(1, Symbol('s2'))],
        # Subst on metavar should wrap in constructor
        [MetaVar(0), 0, Symbol('s1'), SSubst(MetaVar(0), SVar(0), Symbol('s1'))],
        # Subst when evar_id is fresh should do nothing
        [MetaVar(0, s_fresh=(SVar(0), SVar(1))), 0, Symbol('s1'), MetaVar(0, s_fresh=(SVar(0), SVar(1)))],
        # Subst on substs should stack
        [
            ESubst(MetaVar(0), EVar(0), Symbol('s1')),
            0,
            Symbol('s1'),
            SSubst(ESubst(MetaVar(0), EVar(0), Symbol('s1')), SVar(0), Symbol('s1')),
        ],
        [
            SSubst(MetaVar(0), SVar(0), Symbol('s1')),
            0,
            Symbol('s1'),
            SSubst(SSubst(MetaVar(0), SVar(0), Symbol('s1')), SVar(0), Symbol('s1')),
        ],
    ],
)
def test_apply_ssubst(pattern: Pattern, svar_id: int, plug: Pattern, expected: Pattern) -> None:
    assert pattern.apply_ssubst(svar_id, plug) == expected


# Subst 0 for 1 and then 1 for 2
ssubst_stack_seq = lambda term: SSubst(SSubst(term, SVar(0), plug=SVar(1)), SVar(1), plug=SVar(2))

# Subst 1 for 2 and then 0 for 1
ssubst_stack_seq_rev = lambda term: SSubst(SSubst(pattern=term, var=SVar(1), plug=SVar(2)), var=SVar(0), plug=SVar(1))


@pytest.mark.parametrize(
    'stack, mvar, plugs, expected',
    [
        [ssubst_stack_seq, MetaVar(0), {0: SVar(0)}, SVar(2)],
        [ssubst_stack_seq, MetaVar(0), {0: SVar(1)}, SVar(2)],
        [ssubst_stack_seq, MetaVar(1), {0: SVar(1)}, ssubst_stack_seq(MetaVar(1))],
        [ssubst_stack_seq, MetaVar(0), {0: MetaVar(1)}, ssubst_stack_seq(MetaVar(1))],
        [ssubst_stack_seq_rev, MetaVar(0), {0: SVar(0)}, SVar(1)],
        [ssubst_stack_seq_rev, MetaVar(0), {0: MetaVar(1)}, ssubst_stack_seq_rev(MetaVar(1))],
        [stack_mixed1, MetaVar(0), {0: SVar(1)}, EVar(2)],
        [stack_mixed1, MetaVar(0), {0: SVar(2)}, SVar(2)],
        # This fails if metavar instantiations are not propagated into the plug
        [lambda mvar: SSubst(mvar, SVar(0), mvar), MetaVar(0), {0: SVar(0)}, SVar(0)],
    ],
)
def test_instantiate_ssubst(
    stack: Callable[[MetaVar], Pattern], mvar: MetaVar, plugs: dict[int, Pattern], expected: Pattern
) -> None:
    assert stack(mvar).instantiate(plugs) == expected
