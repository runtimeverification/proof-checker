from __future__ import annotations

from proof_generation.basic_interpreter import BasicInterpreter, ExecutionPhase
from proof_generation.pattern import Implies, Symbol
from proof_generation.proofs.propositional import Propositional, neg, phi0, phi1
from proof_generation.proofs.small_theory import SmallTheory
from proof_generation.proved import Proved
from proof_generation.stateful_interpreter import StatefulInterpreter


def test_prove_transitivity() -> None:
    prop = Propositional(BasicInterpreter(phase=ExecutionPhase.Proof))
    phi0_implies_phi1 = lambda: Proved(Implies(Symbol('s0'), Symbol('s1')))
    phi1_implies_phi2 = lambda: Proved(Implies(Symbol('s1'), Symbol('s2')))
    assert prop.imp_transitivity(phi0_implies_phi1, phi1_implies_phi2).conclusion == Implies(
        Symbol('s0'), Symbol('s2')
    )


def test_prove_transitivity_via_theory() -> None:
    th = SmallTheory(StatefulInterpreter(phase=ExecutionPhase.Gamma))
    th.execute_gamma_phase()
    th.execute_claims_phase()
    phi0_implies_phi2 = th.claims()[0]
    assert th.sym0_implies_sym2_proof().conclusion == phi0_implies_phi2


def test_prove_absurd() -> None:
    prop = Propositional(BasicInterpreter(phase=ExecutionPhase.Proof))
    assert prop.absurd().conclusion == Implies(neg(phi0), Implies(phi0, phi1))
