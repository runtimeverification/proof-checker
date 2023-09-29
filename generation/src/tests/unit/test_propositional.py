from __future__ import annotations

from proof_generation.proof import BasicInterpreter, ExecutionPhase, Implication, Proved, StatefulInterpreter, Symbol
from proof_generation.proofs.propositional import Propositional, neg, phi0, phi1
from proof_generation.proofs.small_theory import SmallTheory


def test_prove_transitivity() -> None:
    prop = Propositional(BasicInterpreter(phase=ExecutionPhase.Proof))
    phi0_implies_phi1 = lambda: Proved(Implication(Symbol(0), Symbol(1)))
    phi1_implies_phi2 = lambda: Proved(Implication(Symbol(1), Symbol(2)))
    assert prop.imp_transitivity(phi0_implies_phi1, phi1_implies_phi2).conclusion == Implication(Symbol(0), Symbol(2))


def test_prove_transitivity_via_theory() -> None:
    th = SmallTheory(StatefulInterpreter(phase=ExecutionPhase.Gamma))
    th.execute_gamma_phase()
    th.execute_claims_phase()
    phi0_implies_phi2 = th.claims()[0]
    assert th.sym0_implies_sym2_proof().conclusion == phi0_implies_phi2


def test_prove_absurd() -> None:
    prop = Propositional(BasicInterpreter(phase=ExecutionPhase.Proof))
    assert prop.absurd().conclusion == Implication(neg(phi0), Implication(phi0, phi1))
