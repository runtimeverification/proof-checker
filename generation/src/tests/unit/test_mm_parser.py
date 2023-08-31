import os
from mm_transfer.metamath.parser import load_database
from mm_transfer.metamath.ast import ConstantStatement, FloatingStatement, VariableStatement, AxiomaticStatement, ProvableStatement, Block 


BENCHMARK_LOCATION = 'mm-benchmarks'


def test_parse_impreflex():
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


def test_parse_perceptron():
    """Just checking that the parser works on the file"""
    input_database = load_database(os.path.join(BENCHMARK_LOCATION, 'perceptron.mm'), include_proof=True)
    assert len(input_database.statements) == 100

    # Check the first and the last
    assert isinstance(input_database.statements[0], ConstantStatement)
    assert isinstance(input_database.statements[-1], Block)
    assert isinstance(input_database.statements[-1].statements[0], ProvableStatement)
    assert input_database.statements[-1].statements[0].label == 'goal'


def test_parse_svm5():
    """Just checking that the parser works on the file"""
    input_database = load_database(os.path.join(BENCHMARK_LOCATION, 'svm5.mm'), include_proof=True)
    assert len(input_database.statements) == 100

    assert isinstance(input_database.statements[0], ConstantStatement)
    assert isinstance(input_database.statements[-1], Block)
    assert isinstance(input_database.statements[-1].statements[0], ProvableStatement)
    assert input_database.statements[-1].statements[0].label == 'goal'


def test_parse_transfer():
    """Just checking that the parser works on the file"""
    input_database = load_database(os.path.join(BENCHMARK_LOCATION, 'transfer.mm'), include_proof=True)
    assert len(input_database.statements) == 82

    assert isinstance(input_database.statements[0], ConstantStatement)
    assert isinstance(input_database.statements[-1], Block)
    assert isinstance(input_database.statements[-1].statements[0], ProvableStatement)
    assert input_database.statements[-1].statements[0].label == 'goal'


def test_parse_transfer5000():
    """Just checking that the parser works on the file"""
    input_database = load_database(os.path.join(BENCHMARK_LOCATION, 'transfer5000.mm'), include_proof=True)
    assert len(input_database.statements) == 108

    assert isinstance(input_database.statements[0], ConstantStatement)
    assert isinstance(input_database.statements[-1], Block)
    assert isinstance(input_database.statements[-1].statements[0], ProvableStatement)
    assert input_database.statements[-1].statements[0].label == 'goal'
