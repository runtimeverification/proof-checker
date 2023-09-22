from __future__ import annotations

import os
from typing import TYPE_CHECKING

import pytest

import proof_generation.proof as p
from mm_transfer.converter.converter import MetamathConverter
from mm_transfer.converter.representation import AxiomWithAntecedents
from mm_transfer.metamath.parser import load_database
from mm_transfer.transfer import convert_to_implication, exec_proof

if TYPE_CHECKING:
    from mm_transfer.metamath.parser import Database

BENCHMARK_LOCATION = 'mm-benchmarks'


@pytest.fixture
def parsed_impreflex_database() -> Database:
    return load_database(os.path.join(BENCHMARK_LOCATION, 'impreflex.mm'), include_proof=True)


@pytest.fixture
def parsed_impreflex_compressed_database() -> Database:
    return load_database(os.path.join(BENCHMARK_LOCATION, 'impreflex-compressed.mm'), include_proof=True)


@pytest.fixture
def parsed_transfer_database() -> Database:
    return load_database(os.path.join(BENCHMARK_LOCATION, 'transfer-goal-simple.mm'), include_proof=True)


@pytest.fixture
def parsed_transfer_compressed_database() -> Database:
    return load_database(os.path.join(BENCHMARK_LOCATION, 'transfer-goal-simple-compressed.mm'), include_proof=True)


@pytest.mark.parametrize('db', ["parsed_impreflex_database", "parsed_impreflex_compressed_database"])
def test_exec_proof_impreflex(db: str, request) -> None:
    converter = MetamathConverter(request.getfixturevalue(db))
    assert converter

    extracted_axioms = [converter.get_axiom_by_name(axiom_name).pattern for axiom_name in converter.exported_axioms]
    extracted_claims = [converter.get_lemma_by_name(lemma_name).pattern for lemma_name in converter.lemmas]

    # TODO: Extract this code in transfer.py to a function
    class TranslatedProofSkeleton(p.ProofExp):
        @staticmethod
        def axioms() -> list[p.Pattern]:
            return extracted_axioms

        @staticmethod
        def claims() -> list[p.Pattern]:
            return extracted_claims

    proofexp = TranslatedProofSkeleton(
        p.StatefulInterpreter(p.ExecutionPhase.Proof, [p.Claim(claim) for claim in extracted_claims], extracted_axioms)
    )

    exec_proof(converter, 'imp-reflexivity', proofexp)

    assert isinstance(proofexp.interpreter, p.StatefulInterpreter)
    assert proofexp.interpreter.stack == [p.Proved(proofexp.interpreter, p.Implication(p.MetaVar(0), p.MetaVar(0)))]


@pytest.mark.parametrize('db', ["parsed_transfer_database", "parsed_transfer_compressed_database"])
def test_exec_transfer_proof(db: str, request) -> None:
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
    class TranslatedProofSkeleton(p.ProofExp):
        @staticmethod
        def axioms() -> list[p.Pattern]:
            return extracted_axioms

        @staticmethod
        def claims() -> list[p.Pattern]:
            return extracted_claims

    proofexp = TranslatedProofSkeleton(
        p.StatefulInterpreter(p.ExecutionPhase.Proof, [p.Claim(claim) for claim in extracted_claims], extracted_axioms)
    )

    exec_proof(converter, 'goal', proofexp)

    assert isinstance(proofexp.interpreter, p.StatefulInterpreter)
    assert proofexp.interpreter.stack == [p.Proved(proofexp.interpreter, converter.get_lemma_by_name('goal').pattern)]
