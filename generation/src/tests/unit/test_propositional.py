from __future__ import annotations

from proof_generation.proof import BasicInterpreter, Implication, Proved, Symbol
from proof_generation.proofs.propositional import Propositional


def test_prove_transitivity() -> None:
    prop = Propositional(BasicInterpreter())
    phi0_implies_phi1 = Proved(prop.interpreter, Implication(Symbol(0), Symbol(1)))
    phi1_implies_phi2 = Proved(prop.interpreter, Implication(Symbol(1), Symbol(2)))
    assert prop.imp_transitivity(phi0_implies_phi1, phi1_implies_phi2).conclusion == Implication(Symbol(0), Symbol(2))
