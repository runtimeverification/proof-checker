from __future__ import annotations

from proof_generation.proof import ExecutionPhase, Implication, Proved, StatefulInterpreter, Symbol
from proof_generation.proofs.propositional import Propositional, SmallTheory


def test_prove_transitivity() -> None:
    prop = Propositional(StatefulInterpreter(phase=ExecutionPhase.Proof, axioms=SmallTheory.axioms()))
    phi0_implies_phi1 = Proved(prop.interpreter, Implication(Symbol(0), Symbol(1)))
    phi1_implies_phi2 = Proved(prop.interpreter, Implication(Symbol(1), Symbol(2)))
    assert prop.imp_transitivity(phi0_implies_phi1, phi1_implies_phi2).conclusion == Implication(Symbol(0), Symbol(2))


def test_prove_transitivity_via_theory() -> None:
    th = SmallTheory(StatefulInterpreter(phase=ExecutionPhase.Proof, axioms=SmallTheory.axioms()))
    phi0_implies_phi2 = th.claims()[0]
    assert th.sym0_implies_sym2_proof().conclusion == phi0_implies_phi2
