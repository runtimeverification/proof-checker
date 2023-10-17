from __future__ import annotations

from typing import TYPE_CHECKING

import pytest

from proof_generation.basic_interpreter import BasicInterpreter, ExecutionPhase
from proof_generation.pattern import Implication
from proof_generation.proofs.propositional import And, Or, bot, neg, phi0, phi1, phi2
from proof_generation.tautology import ConjBool, ConjOr, ConjAnd, ConjVar, Tautology, conj_to_pattern

if TYPE_CHECKING:
    from proof_generation.pattern import Pattern
    from proof_generation.tautology import ConjTerm


def assert_eq_pat(p: Pattern, q: Pattern):
    assert p == q, f'{str(p)}\n!=\n{str(q)}\n'

def imp(p1: Pattern, p2: Pattern) -> Pattern:
    return Implication(p1, p2)


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


test_patterns = [
    neg(imp(phi1, imp(bot, bot))),
    imp(phi0, phi0),
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
    l1, r1 = Implication.extract(pf1().conclusion)
    l2, r2 = Implication.extract(pf2().conclusion)
    assert_eq_pat(l1, r2)
    assert_eq_pat(r1, l2)
    assert_eq_pat(l1, p)
    assert_eq_pat(r1, res)
    assert is_conj(p_conj)
    print(f'Proved\n{str(p)}\n<->\n{str(res)}\n\n')
    
    # Testing propag_neg
    p_conj2, pf_neg_1, pf_neg_2 = taut.propag_neg(p_conj)
    res2 = conj_to_pattern(p_conj2)
    l1_neg, r1_neg = Implication.extract(pf_neg_1().conclusion)
    l2_neg, r2_neg = Implication.extract(pf_neg_2().conclusion)
    assert_eq_pat(l1_neg, r2_neg)
    assert_eq_pat(r1_neg, l2_neg)
    assert_eq_pat(l1_neg, res)
    assert_eq_pat(r1_neg, res2)
    assert is_conj_neg(p_conj)
    print(f'Proved\n{str(res)}\n<->\n{str(res2)}\n\n')
