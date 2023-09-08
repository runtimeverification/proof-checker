import os

from mm_transfer.converter.converter import MetamathConverter
from mm_transfer.metamath.ast import ConstantStatement
from mm_transfer.metamath.parser import load_database

BENCHMARK_LOCATION = 'mm-benchmarks'


def test_convert_vars_impreflex() -> None:
    input_database = load_database(os.path.join(BENCHMARK_LOCATION, 'disjointness-alt-lemma.mm'), include_proof=True)
    converter = MetamathConverter(input_database)

    patterns = ('ph0', 'ph1', 'ph2', 'ph3', 'ph4', 'ph5', 'ph6')
    for pattern in patterns:
        assert pattern in converter._patterns and converter._patterns[pattern].name == pattern
    assert len(converter._patterns) == len(patterns)

    symbols = ('sg0',)
    for symbol in symbols:
        assert symbol in converter._symbols and converter._symbols[symbol].name == symbol
    assert len(converter._symbols) == len(symbols)

    mvars = ('xX',)
    for var in mvars:
        assert var in converter._variables and converter._variables[var].name == var
    assert len(converter._variables) == len(mvars)

    evars = ('x', 'y')
    for evar in evars:
        assert evar in converter._element_vars and converter._element_vars[evar].name == evar
    assert len(converter._element_vars) == len(evars)

    setvars = ('X',)
    for setvar in setvars:
        assert setvar in converter._set_vars and converter._set_vars[setvar].name == setvar
    assert len(converter._set_vars) == len(setvars)


def test_convert_symbols_transfer_goal() -> None:
    input_database = load_database(os.path.join(BENCHMARK_LOCATION, 'transfer-goal.mm'), include_proof=True)
    converter = MetamathConverter(input_database)

    assert isinstance(input_database.statements[0], ConstantStatement)
    constants_declaration: ConstantStatement = input_database.statements[0]
    assert len(converter._declared_constants) == len(constants_declaration.constants)

    domain_values = (
        '"0"',
        '"1"',
        '"%24PGM"',
        '"balanceSender"',
        '"ret"',
        '"12345"',
        '"10"',
        '"amount"',
        '"200"',
        '"100"',
        '"balanceTo"',
        '"addressTo"',
        '"90"',
        '"210"',
    )
    assert converter._domain_values == set(domain_values)
