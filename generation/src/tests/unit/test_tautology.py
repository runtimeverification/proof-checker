from __future__ import annotations

from typing import TYPE_CHECKING

import pytest

from proof_generation.basic_interpreter import BasicInterpreter, ExecutionPhase
from proof_generation.pattern import Implication
from proof_generation.proofs.propositional import And, Or, bot, neg, phi0, phi1, phi2
from proof_generation.tautology import ConjBool, ConjOr, ConjVar, Tautology, conj_to_pattern

if TYPE_CHECKING:
    from proof_generation.pattern import Pattern
    from proof_generation.tautology import ConjTerm


def imp(p1: Pattern, p2: Pattern) -> Pattern:
    return Implication(p1, p2)


def is_conj(t: ConjTerm) -> bool:
    if isinstance(t, ConjOr):
        return is_conj(t.left) and is_conj(t.right)
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
def test_to_conj(p: Pattern) -> None:
    taut = Tautology(BasicInterpreter(ExecutionPhase.Proof))
    p_conj, pf1, pf2 = taut.to_conj(p)
    if isinstance(p_conj, ConjBool):
        if p_conj.negated:
            assert not pf2
            pf = pf1().conclusion
            assert pf == p
            print(f'Proved\n{str(p)}\n\n')
        else:
            assert not pf2
            pf = pf1().conclusion
            assert pf == neg(p)
            print(f'Proved\n~({str(p)})\n\n')

    else:
        assert pf2
        res = conj_to_pattern(p_conj)
        l1, r1 = Implication.extract(pf1().conclusion)
        l2, r2 = Implication.extract(pf2().conclusion)
        assert l1 == r2
        assert r1 == l2
        assert l1 == p
        assert r1 == res
        assert is_conj(p_conj)
        print(f'Proved\n{str(p)}\n<->\n{str(res)}\n\n')
