from __future__ import annotations

import os
from typing import TYPE_CHECKING

import pytest

from mm_translate.converter.converter import MetamathConverter
from mm_translate.converter.representation import AxiomWithAntecedents
from mm_translate.metamath.parser import load_database
from mm_translate.translate import convert_to_implication, exec_proof
from proof_generation.basic_interpreter import ExecutionPhase
from proof_generation.claim import Claim
from proof_generation.pattern import Implication, MetaVar
from proof_generation.proof import ProofExp
from proof_generation.proved import Proved
from proof_generation.stateful_interpreter import StatefulInterpreter

if TYPE_CHECKING:
    from pytest import FixtureRequest

    from mm_translate.metamath.parser import Database
    from proof_generation.pattern import Pattern

BENCHMARK_LOCATION = 'mm-benchmarks'


@pytest.fixture
def parsed_impreflex_database() -> Database:
    return load_database(os.path.join(BENCHMARK_LOCATION, 'impreflex.mm'), include_proof=True)


@pytest.fixture
def parsed_impreflex_compressed_database() -> Database:
    return load_database(os.path.join(BENCHMARK_LOCATION, 'impreflex-compressed.mm'), include_proof=True)


@pytest.fixture
def parsed_transfer_database() -> Database:
    return load_database(os.path.join(BENCHMARK_LOCATION, 'transfer-simple-goal.mm'), include_proof=True)


@pytest.fixture
def parsed_transfer_compressed_database() -> Database:
    return load_database(os.path.join(BENCHMARK_LOCATION, 'transfer-simple-compressed-goal.mm'), include_proof=True)


@pytest.mark.parametrize('db', ['parsed_impreflex_database', 'parsed_impreflex_compressed_database'])
def test_exec_proof_impreflex(db: str, request: FixtureRequest) -> None:
    converter = MetamathConverter(request.getfixturevalue(db))
    assert converter

    extracted_axioms = [converter.get_axiom_by_name(axiom_name).pattern for axiom_name in converter.exported_axioms]
    extracted_claims = [converter.get_lemma_by_name(lemma_name).pattern for lemma_name in converter.lemmas]

    # TODO: Extract this code in transfer.py to a function

    class TranslatedProofSkeleton(ProofExp):
        @staticmethod
        def axioms() -> list[Pattern]:
            return extracted_axioms

        @staticmethod
        def claims() -> list[Pattern]:
            return extracted_claims

        def execute_proofs_phase(self) -> None:
            assert self.interpreter.phase == ExecutionPhase.Proof
            exec_proof(converter, 'imp-reflexivity', self)

    proofexp = TranslatedProofSkeleton(
        StatefulInterpreter(
            ExecutionPhase.Gamma,
            [Claim(claim) for claim in extracted_claims],
        )
    )

    proofexp.execute_full()

    assert isinstance(proofexp.interpreter, StatefulInterpreter)
    assert proofexp.interpreter.stack == [Proved(Implication(MetaVar(0), MetaVar(0)))]


@pytest.mark.parametrize('db', ['parsed_transfer_database', 'parsed_transfer_compressed_database'])
def test_exec_transfer_proof(db: str, request: FixtureRequest) -> None:
    converter = MetamathConverter(request.getfixturevalue(db))
    assert converter

    extracted_axioms = []
    for axiom_name in converter.exported_axioms:
        axiom = converter.get_axiom_by_name(axiom_name)
        if isinstance(axiom, AxiomWithAntecedents):
            extracted_axioms.append(convert_to_implication(axiom.antecedents, axiom.pattern))
            continue
        extracted_axioms.append(axiom.pattern)

    extracted_claims = [converter.get_lemma_by_name(lemma_name).pattern for lemma_name in converter.lemmas]

    # TODO: Extract this code in transfer.py to a function
    class TranslatedProofSkeleton(ProofExp):
        @staticmethod
        def axioms() -> list[Pattern]:
            return extracted_axioms

        @staticmethod
        def claims() -> list[Pattern]:
            return extracted_claims

        def execute_proofs_phase(self) -> None:
            assert self.interpreter.phase == ExecutionPhase.Proof
            exec_proof(converter, 'goal', self)

    proofexp = TranslatedProofSkeleton(
        StatefulInterpreter(
            ExecutionPhase.Gamma,
            [Claim(claim) for claim in extracted_claims],
        )
    )

    proofexp.execute_full()

    assert isinstance(proofexp.interpreter, StatefulInterpreter)
    assert proofexp.interpreter.stack == [Proved(converter.get_lemma_by_name('goal').pattern)]
