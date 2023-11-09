from __future__ import annotations

from typing import TYPE_CHECKING

import pytest

from proof_generation.basic_interpreter import BasicInterpreter, ExecutionPhase
from proof_generation.pattern import Implies, bot, imp, phi0, phi1, phi2
from proof_generation.proofs.propositional import And, Equiv, Or, neg, top
from proof_generation.tautology import (
    CFAnd,
    CFBot,
    CFOr,
    CFVar,
    MetaVar,
    Tautology,
    clause_list_to_pattern,
    clause_to_pattern,
    conj_to_pattern,
    foldr_op,
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
def test_cnf_converter(p: Pattern) -> None:
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
    pf1_conc = pf1().conclusion
    assert pf1_conc == Implies(p, res)
    pf2_conc = pf2().conclusion
    assert pf2_conc == Implies(res, p)
    assert is_conj_form(p_conj)

    # Testing propag_neg
    p_conj2, pf_neg_1, pf_neg_2 = taut.propag_neg(p_conj)
    res2 = conj_to_pattern(p_conj2)
    pf_neg_1_conc = pf_neg_1().conclusion
    assert pf_neg_1_conc == Implies(res, res2)
    pf_neg_2_conc = pf_neg_2().conclusion
    assert pf_neg_2_conc == Implies(res2, res)
    assert is_conj_neg(p_conj2)

    # Testing to_cnf
    p_cnf, pf_cnf_1, pf_cnf_2 = taut.to_cnf(p_conj2)
    res3 = conj_to_pattern(p_cnf)
    pf_cnf_1_conc = pf_cnf_1().conclusion
    assert pf_cnf_1_conc == Implies(res2, res3)
    pf_cnf_2_conc = pf_cnf_2().conclusion
    assert pf_cnf_2_conc == Implies(res3, res2)
    assert is_cnf(p_cnf)

    # Testing to_clauses
    p_cl, pf_cl_1, pf_cl_2 = taut.to_clauses(p_cnf)
    res4 = clause_list_to_pattern(p_cl)
    pf_cl_1_conc = pf_cl_1().conclusion
    assert pf_cl_1_conc == Implies(res3, res4)
    pf_cl_2_conc = pf_cl_2().conclusion
    assert pf_cl_2_conc == Implies(res4, res3)


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


@pytest.mark.parametrize('cl, resolvent', simplify_clause_test_cases)
def test_simplify_clause(cl: list[int], resolvent: int) -> None:
    taut = Tautology(BasicInterpreter(ExecutionPhase.Proof))
    final_cl, pf = taut.simplify_clause(cl, resolvent)
    conc = pf().conclusion
    pf_l, pf_r = Equiv.extract(conc)
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


@pytest.mark.parametrize('l', [1, 2, 5])
def test_conjunction_implies_nth(l: int) -> None:
    taut = Tautology(BasicInterpreter(ExecutionPhase.Proof))
    term = foldr_op(And, [MetaVar(i) for i in range(l)])
    for i in range(l):
        pf = taut.conjunction_implies_nth(term, i, l)
        conc = pf().conclusion
        assert conc == Implies(term, MetaVar(i))


resolvable_test_cases = [
    ({}, {}, False),
    ({}, {1}, False),
    ({1}, {-1}, True),
    ({-2}, {2}, True),
    ({1, 2, 3}, {-2, -1}, False),
    ({1, 2, 3, 4}, {-3, 2, 4}, True),
]


@pytest.mark.parametrize('c1, c2, expect_success', resolvable_test_cases)
def test_resolvable(c1: frozenset[int], c2: frozenset[int], expect_success: bool) -> None:
    taut = Tautology(BasicInterpreter(ExecutionPhase.Proof))
    res = taut.resolvable(c1, c2)
    if not expect_success:
        assert res is None
        return
    assert res is not None
    resolvant, res_set = res
    assert c1.union(c2).difference({resolvant, -resolvant}) == res_set


merge_clauses_test_cases = [
    ([1], [2]),
    ([3], [1, 2]),
    ([3, 2], [2]),
    ([3, 2, 2], [1, 2, 3]),
]


@pytest.mark.parametrize('list_l, list_r', merge_clauses_test_cases)
def test_merge_clauses(list_l: list[int], list_r: list[int]) -> None:
    taut = Tautology(BasicInterpreter(ExecutionPhase.Proof))
    term_l = clause_to_pattern(list_l)
    term_r = clause_to_pattern(list_r)
    final_term = clause_to_pattern(list_l + list_r)
    pf = taut.merge_clauses(term_l, len(list_l), term_r)
    conc = pf().conclusion
    assert conc == Equiv(Or(term_l, term_r), final_term)


trivial_clause_test_cases = [
    [-1, 1],
    [2, -2],
    [1, 2, 3, -2],
    # The following test case takes a very long time to run for some reason
    # [1, 2, 3, -2, -1, -1],
    [-1, -1, -1, 1, -1],
]


@pytest.mark.parametrize('test_case', trivial_clause_test_cases)
def test_prove_trivial_clause(test_case: list[int]) -> None:
    taut = Tautology(BasicInterpreter(ExecutionPhase.Proof))
    pf = taut.prove_trivial_clause(test_case)
    conc = pf().conclusion
    assert conc == clause_to_pattern(test_case)


resolution_test_cases = [
    ([], True),
    ([[1]], None),
    ([[1, -1]], True),
    ([[1, -1], [-2, 1, 2, -2]], True),
    ([[-1], [1]], False),
    ([[1], [-1]], False),
    ([[1], [1, -1], [-1]], False),
    ([[1], [-2], [2, -1], [3]], False),
]


@pytest.mark.parametrize('clauses, expected_res', resolution_test_cases)
def test_resolution(clauses: list[list[int]], expected_res: bool | None) -> None:
    taut = Tautology(BasicInterpreter(ExecutionPhase.Proof))
    res = taut.start_resolution_algorithm(clauses)
    if expected_res is None:
        assert res is None
        return
    assert res is not None
    proved_true, pf = res
    assert expected_res == proved_true
    conc = pf().conclusion
    term = clause_list_to_pattern(clauses)
    if proved_true:
        assert conc == term
    else:
        assert conc == neg(term)


phi3 = MetaVar(3)
phi4 = MetaVar(4)

tautology_test_cases = [
    (top, True),
    (bot, False),
    (Or(top, phi0), True),
    (phi0, None),
    (Implies(phi0, phi0), True),
    (Or(phi0, neg(phi0)), True),
    (And(phi0, neg(phi0)), False),
    (
        Implies(
            (Implies(Implies(Implies(Implies(phi0, phi1), neg(phi2)), phi3), phi4)),
            Implies(Implies(phi4, phi0), Implies(phi2, phi0)),
        ),
        True,
    ),
]


@pytest.mark.parametrize('pat, expected_res', tautology_test_cases)
def test_tautology_prover(pat: Pattern, expected_res: bool | None) -> None:
    taut = Tautology(BasicInterpreter(ExecutionPhase.Proof))
    res = taut.prove_tautology(pat)
    if expected_res is None:
        assert res is None
        return
    assert res is not None
    proved_true, pf = res
    assert expected_res == proved_true
    conc = pf().conclusion
    if proved_true:
        assert conc == pat
    else:
        assert conc == neg(pat)
