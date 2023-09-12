from typing import Callable
import pytest
from proof_generation.pattern import Pattern, EVar, SVar, Symbol, Implication, Application, Exists, Mu, MetaVar, ESubst, SSubst


@pytest.mark.parametrize('pattern, evar_id, plug, expected', [
    # Atomic cases
    [EVar(0), 0, Symbol(1), Symbol(1)],
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
    [Exists(EVar(1), Symbol(1)), 0, Symbol(2), Exists(EVar(1), Symbol(1))],
    [Exists(EVar(1), Symbol(1)), 1, Symbol(2), Exists(EVar(1), Symbol(1))],
    [Mu(SVar(1), EVar(1)), 0, Symbol(2), Mu(SVar(1), EVar(1))],
    [Mu(SVar(1), EVar(1)), 1, Symbol(2), Mu(SVar(1), Symbol(2))],

    # Subst on metavar should wrap in constructor
    [MetaVar(0), 0, Symbol(1), ESubst(MetaVar(0), EVar(0), Symbol(1))],
    # Subst when evar_id is fresh should do nothing
    [MetaVar(0, e_fresh=[0, 1]), 0, Symbol(1), MetaVar(0, e_fresh=[0, 1])],
    # Subst on substs should stack
    [ESubst(MetaVar(0), EVar(0), Symbol(1)), 0, Symbol(1), ESubst(ESubst(MetaVar(0), EVar(0), Symbol(1)), EVar(0), Symbol(1))],
    [SSubst(MetaVar(0), EVar(0), Symbol(1)), 0, Symbol(1), ESubst(SSubst(MetaVar(0), EVar(0), Symbol(1)), EVar(0), Symbol(1))]
])

def test_apply_esubst_simple(pattern: Pattern, evar_id: int, plug: Pattern, expected: Pattern):
    assert pattern.apply_esubst(evar_id, plug) == expected

stack1 = lambda mvar: ESubst(ESubst(mvar, EVar(0), plug=EVar(1)), EVar(1), plug=EVar(2))

@pytest.mark.parametrize('stack, mvar, plugs, expected', [
    [stack1, MetaVar(0), {0: EVar(1)}, EVar(2)]
])
def test_apply_esubst_stack(stack: Callable[[MetaVar], Pattern], mvar, plugs, expected):
    assert stack(mvar).instantiate(plugs) == expected
