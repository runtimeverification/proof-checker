import os

from proof_generation.metamath.ast import (
    AxiomaticStatement,
    Block,
    ConstantStatement,
    FloatingStatement,
    ProvableStatement,
    VariableStatement,
)
from proof_generation.metamath.parser import load_database

BENCHMARK_LOCATION = 'generation/mm-benchmarks'


def test_parse_impreflex() -> None:
    """Checking entire content for this small example"""
    input_database = load_database(os.path.join(BENCHMARK_LOCATION, 'impreflex.mm'), include_proof=True)
    assert len(input_database.statements) == 13

    # Check the structure of the database
    statements = iter(input_database.statements)
    assert isinstance(next(statements), ConstantStatement)
    assert isinstance(next(statements), VariableStatement)

    for label in ('ph0-is-pattern', 'ph1-is-pattern', 'ph2-is-pattern'):
        fs = next(statements)
        assert isinstance(fs, FloatingStatement)
        assert fs.label == label

    for _ in range(3):
        constant = next(statements)
        assert isinstance(constant, ConstantStatement)

    for label in ('imp-is-pattern', 'proof-rule-prop-1', 'proof-rule-prop-2'):
        fs = next(statements)
        assert isinstance(fs, AxiomaticStatement)
        assert fs.label == label

    block = next(statements)
    assert isinstance(block, Block)
    assert len(block.statements) == 3

    provable_statement = next(statements)
    assert input_database.statements[-1] == provable_statement
    assert isinstance(provable_statement, ProvableStatement)
    assert provable_statement.label == 'imp-reflexivity'


def test_parse_perceptron() -> None:
    """Just checking that the parser works on the file"""
    input_database = load_database(os.path.join(BENCHMARK_LOCATION, 'perceptron.mm'), include_proof=True)
    assert len(input_database.statements) == 100

    # Check the first and the last
    assert isinstance(input_database.statements[0], ConstantStatement)
    assert isinstance(input_database.statements[-1], Block)
    assert isinstance(input_database.statements[-1].statements[0], ProvableStatement)
    assert input_database.statements[-1].statements[0].label == 'goal'


def test_parse_svm5() -> None:
    """Just checking that the parser works on the file"""
    input_database = load_database(os.path.join(BENCHMARK_LOCATION, 'svm5.mm'), include_proof=True)
    assert len(input_database.statements) == 100

    assert isinstance(input_database.statements[0], ConstantStatement)
    assert isinstance(input_database.statements[-1], Block)
    assert isinstance(input_database.statements[-1].statements[0], ProvableStatement)
    assert input_database.statements[-1].statements[0].label == 'goal'


def test_parse_transfer() -> None:
    """Just checking that the parser works on the file"""
    input_database = load_database(os.path.join(BENCHMARK_LOCATION, 'transfer.mm'), include_proof=True)
    assert len(input_database.statements) == 11515

    assert isinstance(input_database.statements[0], ConstantStatement)
    assert isinstance(input_database.statements[-1], ProvableStatement)
    assert input_database.statements[-1].label == 'goal'


def test_parse_transfer5000() -> None:
    """Just checking that the parser works on the file"""
    input_database = load_database(os.path.join(BENCHMARK_LOCATION, 'transfer5000.mm'), include_proof=True)
    assert len(input_database.statements) == 108

    assert isinstance(input_database.statements[0], ConstantStatement)
    assert isinstance(input_database.statements[-1], Block)
    assert isinstance(input_database.statements[-1].statements[0], ProvableStatement)
    assert input_database.statements[-1].statements[0].label == 'goal'


def test_parse_transfer_goal() -> None:
    """Just checking that the parser works on the file"""
    input_database = load_database(os.path.join(BENCHMARK_LOCATION, 'transfer-goal.mm'), include_proof=True)
    assert len(input_database.statements) == 221

    assert isinstance(input_database.statements[0], ConstantStatement)
    assert isinstance(input_database.statements[-1], Block)
    assert isinstance(input_database.statements[-1].statements[0], ProvableStatement)
    assert input_database.statements[-1].statements[0].label == 'goal'


def test_parse_transfer_largest_slice() -> None:
    """Just checking that the parser works on the file"""
    input_database = load_database(os.path.join(BENCHMARK_LOCATION, 'transfer-largest-slice.mm'), include_proof=True)
    assert len(input_database.statements) == 189

    assert isinstance(input_database.statements[0], ConstantStatement)
    assert isinstance(input_database.statements[-1], Block)
    assert isinstance(input_database.statements[-1].statements[0], ProvableStatement)
    assert input_database.statements[-1].statements[0].label == 'symbolic-step-12'


def test_parse_disjointness_alt_lemma_slice() -> None:
    """Just checking that the parser works on the file"""
    input_database = load_database(os.path.join(BENCHMARK_LOCATION, 'disjointness-alt-lemma.mm'), include_proof=True)
    assert len(input_database.statements) == 75

    assert isinstance(input_database.statements[0], ConstantStatement)
    assert isinstance(input_database.statements[-1], Block)
    assert isinstance(input_database.statements[-1].statements[-1], ProvableStatement)
    assert input_database.statements[-1].statements[-1].label == 'disjointness-alt-lemma'
