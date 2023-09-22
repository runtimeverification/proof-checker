from __future__ import annotations

import os
from typing import TYPE_CHECKING

import pytest

import proof_generation.proof as p
from mm_transfer.converter.converter import MetamathConverter
from mm_transfer.metamath.parser import load_database
from mm_transfer.transfer import exec_proof

if TYPE_CHECKING:
    from mm_transfer.metamath.parser import Database

BENCHMARK_LOCATION = 'mm-benchmarks'


@pytest.fixture
def parsed_impreflex_database() -> Database:
    return load_database(os.path.join(BENCHMARK_LOCATION, 'impreflex.mm'), include_proof=True)


def test_exec_proof(parsed_impreflex_database: Database) -> None:
    converter = MetamathConverter(parsed_impreflex_database)
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
