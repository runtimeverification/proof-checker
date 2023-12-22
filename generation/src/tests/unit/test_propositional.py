from __future__ import annotations

from typing import TYPE_CHECKING

import pytest

from proof_generation.aml import App, Implies, Symbol
from proof_generation.interpreter import BasicInterpreter, ExecutionPhase, StatefulInterpreter
from proof_generation.proof import ProofThunk
from proof_generation.proofs.propositional import Propositional, _and, _or, neg, phi0, phi1, phi2
from proof_generation.proofs.small_theory import SmallTheory
from proof_generation.proved import Proved

if TYPE_CHECKING:
    from proof_generation.aml import Pattern

prop = Propositional()
sigma0 = Symbol('s0')


def make_pt(p: Pattern) -> ProofThunk:
    return ProofThunk((lambda interpreter: Proved(p)), p)


def test_prove_transitivity() -> None:
    phi0_implies_phi1 = make_pt(Implies(Symbol('s0'), Symbol('s1')))
    phi1_implies_phi2 = make_pt(Implies(Symbol('s1'), Symbol('s2')))
    assert prop.imp_transitivity(phi0_implies_phi1, phi1_implies_phi2)(
        BasicInterpreter(phase=ExecutionPhase.Proof)
    ).conclusion == Implies(Symbol('s0'), Symbol('s2'))


def test_prove_transitivity_via_theory() -> None:
    th = SmallTheory()
    interpreter = StatefulInterpreter(phase=ExecutionPhase.Gamma)
    th.execute_gamma_phase(interpreter)
    th.execute_claims_phase(interpreter)
    phi0_implies_phi2 = th._claims[0]
    assert th.sym0_implies_sym2_proof()(interpreter).conclusion == phi0_implies_phi2


def test_prove_absurd() -> None:
    assert prop.absurd()(BasicInterpreter(phase=ExecutionPhase.Proof)).conclusion == Implies(
        neg(phi0), Implies(phi0, phi1)
    )


def dummy_proof(pat: Pattern) -> ProofThunk:
    return ProofThunk(lambda interpreter: Proved(pat), pat)


@pytest.mark.parametrize(
    'pf, pattern, expected',
    [
        (prop.imp_refl(), sigma0, Implies(sigma0, sigma0)),
        (
            dummy_proof(Implies(_and(App(phi0, phi1), phi2), _or(phi0, _and(phi1, phi2)))),
            _and(App(sigma0, phi0), Implies(phi1, phi1)),
            Implies(_and(App(sigma0, phi0), Implies(phi1, phi1)), _or(sigma0, _and(phi0, Implies(phi1, phi1)))),
        ),
    ],
)
def test_imp_match_l(pf: ProofThunk, pattern: Pattern, expected: Pattern) -> None:
    interpreter = BasicInterpreter(ExecutionPhase.Proof)
    assert Proved(expected) == prop.imp_match_l(pf, pattern)(interpreter)


@pytest.mark.parametrize(
    'pf, pattern, expected',
    [
        (prop.imp_refl(), sigma0, Implies(sigma0, sigma0)),
        (
            dummy_proof(Implies(_and(App(phi0, phi1), phi2), _or(phi0, _and(phi1, phi2)))),
            _or(sigma0, _and(phi0, Implies(phi1, phi1))),
            Implies(_and(App(sigma0, phi0), Implies(phi1, phi1)), _or(sigma0, _and(phi0, Implies(phi1, phi1)))),
        ),
    ],
)
def test_imp_match_r(pf: ProofThunk, pattern: Pattern, expected: Pattern) -> None:
    interpreter = BasicInterpreter(ExecutionPhase.Proof)
    assert Proved(expected) == prop.imp_match_r(pf, pattern)(interpreter)
