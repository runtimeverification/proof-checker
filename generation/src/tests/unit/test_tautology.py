from __future__ import annotations

from typing import TYPE_CHECKING

import pytest

from proof_generation.basic_interpreter import BasicInterpreter, ExecutionPhase
from proof_generation.pattern import Implies, bot, imp, phi0, phi1, phi2
from proof_generation.proofs.propositional import _and, _or, equiv, neg, top
from proof_generation.tautology import (
    CFAnd,
    CFBot,
    CFOr,
    CFVar,
    Tautology,
    clause_list_to_pattern,
    clause_to_pattern,
    conj_to_pattern,
)

if TYPE_CHECKING:
    from proof_generation.pattern import Pattern
    from proof_generation.tautology import ConjForm


def is_conj_form(t: ConjForm) -> bool:
    if isinstance(t, CFOr):
        return is_conj_form(t.left) and is_conj_form(t.right)
    if isinstance(t, CFVar):
        return True
    return False


def is_conj_neg(t: ConjForm) -> bool:
    if isinstance(t, CFAnd):
        return (not t.negated) and is_conj_neg(t.left) and is_conj_neg(t.right)
    if isinstance(t, CFOr):
        return (not t.negated) and is_conj_neg(t.left) and is_conj_neg(t.right)
    if isinstance(t, CFVar):
        return True
    return False


def is_clause(t: ConjForm) -> bool:
    if isinstance(t, CFOr):
        return (not t.negated) and is_clause(t.left) and is_clause(t.right)
    if isinstance(t, CFVar):
        return True
    return False


def is_cnf(t: ConjForm) -> bool:
    if isinstance(t, CFAnd):
        return (not t.negated) and is_cnf(t.left) and is_cnf(t.right)
    if isinstance(t, CFOr):
        return (not t.negated) and is_clause(t.left) and is_clause(t.right)
    if isinstance(t, CFVar):
        return True
    return False


test_patterns = [
    top(),
    imp(phi0, phi0),
    neg(imp(neg(phi0), phi0)),
    imp(imp(phi0, phi0), phi0),
    neg(imp(phi1, imp(bot(), bot()))),
    _or(imp(phi0, phi1), neg(phi2)),
    imp(_or(phi0, phi2), phi0),
    neg(neg(imp(_or(neg(phi0), phi0), _and(phi1, imp(phi1, phi2))))),
    neg(neg(neg(imp(_or(neg(phi0), phi0), _and(phi1, imp(phi1, phi2)))))),
]


@pytest.mark.parametrize('p', test_patterns)
def test_tautology_prover(p: Pattern) -> None:
    taut = Tautology(BasicInterpreter(ExecutionPhase.Proof))

    # Testing to_conj_form
    p_conj, pf1, pf2 = taut.to_conj_form(p)
    if isinstance(p_conj, CFBot):
        if p_conj.negated:
            assert pf2 is None
            conc = pf1().conclusion
            assert conc == p
            return
        else:
            assert pf2 is None
            pf = pf1().conclusion
            assert pf == neg(p)
            return
    assert pf2 is not None
    res = conj_to_pattern(p_conj)
    l1, r1 = Implies.extract(pf1().conclusion)
    l2, r2 = Implies.extract(pf2().conclusion)
    assert l1 == r2
    assert r1 == l2
    assert l1 == p
    assert r1 == res
    assert is_conj_form(p_conj)

    # Testing propag_neg
    p_conj2, pf_neg_1, pf_neg_2 = taut.propag_neg(p_conj)
    res2 = conj_to_pattern(p_conj2)
    l1_neg, r1_neg = Implies.extract(pf_neg_1().conclusion)
    l2_neg, r2_neg = Implies.extract(pf_neg_2().conclusion)
    assert l1_neg == r2_neg
    assert r1_neg == l2_neg
    assert l1_neg == res
    assert r1_neg == res2
    assert is_conj_neg(p_conj2)

    # Testing to_cnf
    p_cnf, pf_cnf_1, pf_cnf_2 = taut.to_cnf(p_conj2)
    res3 = conj_to_pattern(p_cnf)
    l1_cnf, r1_cnf = Implies.extract(pf_cnf_1().conclusion)
    l2_cnf, r2_cnf = Implies.extract(pf_cnf_2().conclusion)
    assert l1_cnf == r2_cnf
    assert r1_cnf == l2_cnf
    assert l1_cnf == res2
    assert r1_cnf == res3
    assert is_cnf(p_cnf)

    # Testing to_clauses
    p_cl, pf_cl_1, pf_cl_2 = taut.to_clauses(p_cnf)
    res4 = clause_list_to_pattern(p_cl)
    l1_cl, r1_cl = Implies.extract(pf_cl_1().conclusion)
    l2_cl, r2_cl = Implies.extract(pf_cl_2().conclusion)
    assert l1_cl == r2_cl
    assert r1_cl == l2_cl
    assert l1_cl == res3
    assert r1_cl == res4


simplify_clause_test_cases = [
    ([2, 1, 1, 3], 4),
    ([1], 1),
    ([2], 2),
    ([-2, 1], 1),
    ([1, 1], 1),
    ([-2, -2, -2, 1], -2),
    ([1, 1, 1, 1], 1),
    ([1, 2, 2], 1),
    ([1, 2, -3, 1], 1),
    ([1, 2, 3, 2], 2),
    # The following test case takes 10 minutes to run for some reason
    # ([2, 2, 1, 3, 1, 1], 1),
]


@pytest.mark.parametrize('test_case', simplify_clause_test_cases)
def test_simplify_clause(test_case: tuple[list[int], int]) -> None:
    cl, resolvent = test_case
    taut = Tautology(BasicInterpreter(ExecutionPhase.Proof))
    final_cl, pf = taut.simplify_clause(cl, resolvent)
    conc = pf().conclusion
    pf_l, pf_r = equiv.assert_matches(conc)
    assert clause_to_pattern(cl) == pf_l
    assert clause_to_pattern(final_cl) == pf_r
    resolvent_present = False
    stripped_cl = []
    for i in range(len(cl)):
        if cl[i] == resolvent:
            resolvent_present = True
        else:
            stripped_cl.append(cl[i])
    if not resolvent_present:
        assert cl == final_cl
        return
    assert final_cl[0] == resolvent
    assert final_cl[1:] == stripped_cl
