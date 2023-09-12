from __future__ import annotations

from typing import TYPE_CHECKING

import pytest

from proof_generation.pattern import Application, ESubst, EVar, Exists, Implication, MetaVar, Mu, SSubst, SVar, Symbol

if TYPE_CHECKING:
    from collections.abc import Callable

    from proof_generation.pattern import Pattern


@pytest.mark.parametrize(
    'pattern, evar_id, plug, expected',
    [
        # Atomic cases
        [EVar(0), 0, Symbol(1), Symbol(1)],
        [EVar(0), 0, EVar(2), EVar(2)],
        [EVar(0), 1, EVar(2), EVar(0)],
        [SVar(0), 0, Symbol(0), SVar(0)],
        [SVar(1), 0, EVar(0), SVar(1)],
        [Symbol(0), 0, Symbol(1), Symbol(0)],
        # Distribute over subpatterns
        [Implication(EVar(7), Symbol(1)), 7, Symbol(0), Implication(Symbol(0), Symbol(1))],
        [Implication(EVar(7), Symbol(1)), 6, Symbol(0), Implication(EVar(7), Symbol(1))],
        [Application(EVar(7), Symbol(1)), 7, Symbol(0), Application(Symbol(0), Symbol(1))],
        [Application(EVar(7), Symbol(1)), 6, Symbol(0), Application(EVar(7), Symbol(1))],
        # Distribute over subpatterns unless evar_id = binder
        [Exists(EVar(1), EVar(1)), 0, Symbol(2), Exists(EVar(1), EVar(1))],
        [Exists(EVar(0), EVar(1)), 1, Symbol(2), Exists(EVar(0), Symbol(2))],
        [Mu(SVar(1), EVar(1)), 0, Symbol(2), Mu(SVar(1), EVar(1))],
        [Mu(SVar(1), EVar(1)), 1, Symbol(2), Mu(SVar(1), Symbol(2))],
        # Subst on metavar should wrap in constructor
        [MetaVar(0), 0, Symbol(1), ESubst(MetaVar(0), EVar(0), Symbol(1))],
        # Subst when evar_id is fresh should do nothing
        [MetaVar(0, e_fresh=(EVar(0), EVar(1))), 0, Symbol(1), MetaVar(0, e_fresh=(EVar(0), EVar(1)))],
        # Subst on substs should stack
        [
            ESubst(MetaVar(0), EVar(0), Symbol(1)),
            0,
            Symbol(1),
            ESubst(ESubst(MetaVar(0), EVar(0), Symbol(1)), EVar(0), Symbol(1)),
        ],
        [
            SSubst(MetaVar(0), SVar(0), Symbol(1)),
            0,
            Symbol(1),
            ESubst(SSubst(MetaVar(0), SVar(0), Symbol(1)), EVar(0), Symbol(1)),
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
        [EVar(0), 0, Symbol(1), EVar(0)],
        [EVar(0), 1, EVar(2), EVar(0)],
        [SVar(0), 0, Symbol(0), Symbol(0)],
        [SVar(1), 0, EVar(0), SVar(1)],
        [Symbol(0), 0, Symbol(1), Symbol(0)],
        # Distribute over subpatterns
        [Implication(SVar(7), Symbol(1)), 7, Symbol(0), Implication(Symbol(0), Symbol(1))],
        [Implication(SVar(7), Symbol(1)), 6, Symbol(0), Implication(SVar(7), Symbol(1))],
        [Application(SVar(7), Symbol(1)), 7, Symbol(0), Application(Symbol(0), Symbol(1))],
        [Application(SVar(7), Symbol(1)), 6, Symbol(0), Application(SVar(7), Symbol(1))],
        # Distribute over subpatterns unless svar_id = binder
        [Exists(EVar(1), SVar(0)), 0, Symbol(2), Exists(EVar(1), Symbol(2))],
        [Exists(EVar(1), Symbol(1)), 1, Symbol(2), Exists(EVar(1), Symbol(1))],
        [Mu(SVar(1), SVar(1)), 0, Symbol(2), Mu(SVar(1), SVar(1))],
        [Mu(SVar(1), SVar(1)), 1, Symbol(2), Mu(SVar(1), Symbol(2))],
        # Subst on metavar should wrap in constructor
        [MetaVar(0), 0, Symbol(1), SSubst(MetaVar(0), SVar(0), Symbol(1))],
        # Subst when evar_id is fresh should do nothing
        [MetaVar(0, s_fresh=(SVar(0), SVar(1))), 0, Symbol(1), MetaVar(0, s_fresh=(SVar(0), SVar(1)))],
        # Subst on substs should stack
        [
            ESubst(MetaVar(0), EVar(0), Symbol(1)),
            0,
            Symbol(1),
            SSubst(ESubst(MetaVar(0), EVar(0), Symbol(1)), SVar(0), Symbol(1)),
        ],
        [
            SSubst(MetaVar(0), SVar(0), Symbol(1)),
            0,
            Symbol(1),
            SSubst(SSubst(MetaVar(0), SVar(0), Symbol(1)), SVar(0), Symbol(1)),
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
    ],
)
def test_instantiate_ssubst(
    stack: Callable[[MetaVar], Pattern], mvar: MetaVar, plugs: dict[int, Pattern], expected: Pattern
) -> None:
    assert stack(mvar).instantiate(plugs) == expected
