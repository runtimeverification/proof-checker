from __future__ import annotations

from typing import TYPE_CHECKING

import pytest

from proof_generation.basic_interpreter import BasicInterpreter, ExecutionPhase
from proof_generation.pattern import Implies, bot, imp
from proof_generation.proofs.propositional import And, Equiv, Or, neg, phi0, phi1, phi2, top
from proof_generation.tautology import (
    ConjAnd,
    ConjBool,
    ConjOr,
    ConjVar,
    Tautology,
    clause_list_to_pattern,
    conj_to_pattern,
)

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
    imp(Or(phi0, phi2), phi0),
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

    # Testing propag_neg
    p_conj2, pf_neg_1, pf_neg_2 = taut.propag_neg(p_conj)
    res2 = conj_to_pattern(p_conj2)
    l1_neg, r1_neg = Implies.extract(pf_neg_1().conclusion)
    l2_neg, r2_neg = Implies.extract(pf_neg_2().conclusion)
    assert_eq_pat(l1_neg, r2_neg)
    assert_eq_pat(r1_neg, l2_neg)
    assert_eq_pat(l1_neg, res)
    assert_eq_pat(r1_neg, res2)
    assert is_conj_neg(p_conj2)
    print(f'Proved\n{str(res)}\n<->\n{str(res2)}\n\n')

    # Testing to_cnf
    p_cnf, pf_cnf_1, pf_cnf_2 = taut.to_cnf(p_conj2)
    res3 = conj_to_pattern(p_cnf)
    l1_cnf, r1_cnf = Implies.extract(pf_cnf_1().conclusion)
    l2_cnf, r2_cnf = Implies.extract(pf_cnf_2().conclusion)
    assert_eq_pat(l1_cnf, r2_cnf)
    assert_eq_pat(r1_cnf, l2_cnf)
    assert_eq_pat(l1_cnf, res2)
    assert_eq_pat(r1_cnf, res3)
    assert is_cnf(p_cnf)
    print(f'Proved\n{str(res2)}\n<->\n{str(res3)}\n\n')

    # Testing to_clauses
    p_cl, pf_cl_1, pf_cl_2 = taut.to_clauses(p_cnf)
    res4 = clause_list_to_pattern(p_cl)
    l1_cl, r1_cl = Implies.extract(pf_cl_1().conclusion)
    l2_cl, r2_cl = Implies.extract(pf_cl_2().conclusion)
    assert_eq_pat(l1_cl, r2_cl)
    assert_eq_pat(r1_cl, l2_cl)
    assert_eq_pat(l1_cl, res3)
    assert_eq_pat(r1_cl, res4)
    print(f'Proved\n{str(res3)}\n<->\n{str(res4)}\n\n')


@pytest.mark.parametrize('i', range(5))
@pytest.mark.parametrize('is_last', [False, True])
def test_move_last_to_front(i: int, is_last: bool) -> None:
    taut = Tautology(BasicInterpreter(ExecutionPhase.Proof))

    len = i + 1 if is_last else 100

    pf = taut.or_move_to_front(i, len)
    conc = pf().conclusion
    c1, c2 = Equiv.extract(conc)

    print(f'Proved {str(c1)} <-> {str(c2)} \n\n')
