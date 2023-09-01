import os

from mm_transfer.converter.converter import MetamathConverter
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
        assert evar in converter._elemental and converter._elemental[evar].name == evar
    assert len(converter._elemental) == len(evars)
