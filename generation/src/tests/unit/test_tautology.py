from __future__ import annotations

from typing import TYPE_CHECKING

import pytest

from proof_generation.basic_interpreter import BasicInterpreter, ExecutionPhase
from proof_generation.pattern import Implies, bot, imp
from proof_generation.proofs.propositional import And, Or, neg, phi0, phi1, phi2, top
from proof_generation.tautology import CFBot, CFOr, CFVar, Tautology, conj_to_pattern

if TYPE_CHECKING:
    from proof_generation.pattern import Pattern
    from proof_generation.tautology import ConjForm


def is_conj_form(t: ConjForm) -> bool:
    if isinstance(t, CFOr):
        return is_conj_form(t.left) and is_conj_form(t.right)
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
    neg(neg(imp(Or(neg(phi0), phi0), And(phi1, imp(phi1, phi2))))),
    neg(neg(neg(imp(Or(neg(phi0), phi0), And(phi1, imp(phi1, phi2)))))),
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
