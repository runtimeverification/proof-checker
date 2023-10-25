from __future__ import annotations

from typing import TYPE_CHECKING

import pytest

from proof_generation.basic_interpreter import BasicInterpreter, ExecutionPhase
from proof_generation.pattern import Implies, bot, imp
from proof_generation.proofs.propositional import And, Or, neg, phi0, phi1, phi2, top
from proof_generation.tautology import ConjAnd, ConjBool, ConjOr, ConjVar, Tautology, conj_to_pattern

if TYPE_CHECKING:
    from proof_generation.pattern import Pattern
    from proof_generation.tautology import ConjTerm


def assert_eq_pat(p: Pattern, q: Pattern) -> None:
    assert p == q, f'{str(p)}\n!=\n{str(q)}\n'


def is_conj(t: ConjTerm) -> bool:
    if isinstance(t, ConjOr):
        return is_conj(t.left) and is_conj(t.right)
    if isinstance(t, ConjVar):
        return True
    return False


def is_conj_neg(t: ConjTerm) -> bool:
    if isinstance(t, ConjAnd):
        return (not t.negated) and is_conj_neg(t.left) and is_conj_neg(t.right)
    if isinstance(t, ConjOr):
        return (not t.negated) and is_conj_neg(t.left) and is_conj_neg(t.right)
    if isinstance(t, ConjVar):
        return True
    return False


def is_clause(t: ConjTerm) -> bool:
    if isinstance(t, ConjOr):
        return (not t.negated) and is_conj(t.left) and is_conj(t.right)
    if isinstance(t, ConjVar):
        return True
    return False


def is_cnf(t: ConjTerm) -> bool:
    if isinstance(t, ConjAnd):
        return (not t.negated) and is_cnf(t.left) and is_cnf(t.right)
    if isinstance(t, ConjOr):
        return (not t.negated) and is_clause(t.left) and is_clause(t.right)
    if isinstance(t, ConjVar):
        return True
    return False


test_patterns = [
    top,
    imp(phi0, phi0),
    neg(imp(neg(phi0), phi0)),
    imp(imp(phi0, phi0), phi0),
    neg(imp(phi1, imp(bot, bot))),
    Or(imp(phi0, phi1), neg(phi2)),
    neg(neg(imp(Or(neg(phi0), phi0), And(phi1, imp(phi1, phi2))))),
    neg(neg(neg(imp(Or(neg(phi0), phi0), And(phi1, imp(phi1, phi2)))))),
]


@pytest.mark.parametrize('p', test_patterns)
def test_tautology_prover(p: Pattern) -> None:
    taut = Tautology(BasicInterpreter(ExecutionPhase.Proof))

    # Testing to_conj
    p_conj, pf1, pf2 = taut.to_conj(p)
    if isinstance(p_conj, ConjBool):
        if p_conj.negated:
            assert pf2 is None
            pf = pf1().conclusion
            assert_eq_pat(pf, p)
            print(f'Proved\n{str(p)}\n\n')
            return
        else:
            assert pf2 is None
            pf = pf1().conclusion
            assert_eq_pat(pf, neg(p))
            print(f'Proved\n~({str(p)})\n\n')
            return
    assert pf2 is not None
    res = conj_to_pattern(p_conj)
    l1, r1 = Implies.extract(pf1().conclusion)
    l2, r2 = Implies.extract(pf2().conclusion)
    assert_eq_pat(l1, r2)
    assert_eq_pat(r1, l2)
    assert_eq_pat(l1, p)
    assert_eq_pat(r1, res)
    assert is_conj(p_conj)
    print(f'Proved\n{str(p)}\n<->\n{str(res)}\n\n')
