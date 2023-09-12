from __future__ import annotations

import os
from typing import TYPE_CHECKING

import pytest

import proof_generation.pattern as nf
from mm_transfer.converter.converter import MetamathConverter
from mm_transfer.metamath.ast import ConstantStatement
from mm_transfer.metamath.parser import load_database

if TYPE_CHECKING:
    from mm_transfer.metamath.ast import Database

BENCHMARK_LOCATION = 'mm-benchmarks'


@pytest.fixture
def parsed_lemma_database() -> Database:
    return load_database(os.path.join(BENCHMARK_LOCATION, 'disjointness-alt-lemma.mm'), include_proof=True)


@pytest.fixture
def parsed_goal_database() -> Database:
    return load_database(os.path.join(BENCHMARK_LOCATION, 'transfer-goal.mm'), include_proof=True)


def pattern_mismatch(p1: nf.Pattern, p2: nf.Pattern) -> str:
    return f'Pattern mismatch: {str(p1)} != {str(p2)}'


def test_importing_variables(parsed_lemma_database: Database) -> None:
    converter = MetamathConverter(parsed_lemma_database)

    patterns = ('ph0', 'ph1', 'ph2', 'ph3', 'ph4', 'ph5', 'ph6')
    for pattern in patterns:
        assert pattern in converter._scope._metavars
    assert len(converter._scope._metavars) == len(patterns)

    symbols = ('sg0', '\\definedness', '\\inhabitant')
    for symbol in symbols:
        assert symbol in converter._scope._symbols
    assert len(converter._scope._symbols) == len(symbols)

    evars = ('x', 'y', 'xX')
    for evar in evars:
        assert evar in converter._scope._element_vars
    assert len(converter._scope._element_vars) == len(evars)

    setvars = ('X', 'xX')
    for setvar in setvars:
        assert setvar in converter._scope._set_vars
    assert len(converter._scope._set_vars) == len(setvars)


def test_importing_domain_values(parsed_goal_database: Database) -> None:
    converter = MetamathConverter(parsed_goal_database)

    assert isinstance(parsed_goal_database.statements[0], ConstantStatement)
    constants_declaration: ConstantStatement = parsed_goal_database.statements[0]
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
    assert converter._scope._domain_values == set(domain_values)


def test_importing_notations(parsed_lemma_database: Database) -> None:
    converter = MetamathConverter(parsed_lemma_database)
    scope = converter._scope
    definedness = scope._symbols['\\definedness']
    inhabitant = scope._symbols['\\inhabitant']
    assert len(scope._notations) == 11

    def bot() -> nf.Pattern:
        return nf.Mu(nf.SVar(0), nf.SVar(0))

    expected = bot()
    converted = scope.resolve_notation('\\bot')()
    assert expected == converted, pattern_mismatch(expected, converted)

    def neg(p: nf.Pattern) -> nf.Pattern:
        return nf.Implication(p, bot())

    expected = neg(nf.MetaVar(10))
    converted = scope.resolve_notation('\\not')(nf.MetaVar(10))
    assert expected == converted, pattern_mismatch(expected, converted)

    # \imp ( \not ph0 ) ph1
    def or_(p: nf.Pattern, q: nf.Pattern) -> nf.Pattern:
        return nf.Implication(neg(p), q)

    expected = or_(nf.MetaVar(10), nf.MetaVar(11))
    converted = scope.resolve_notation('\\or')(nf.MetaVar(10), nf.MetaVar(11))

    #  \not ( \or ( \not ph0 ) ( \not ph1 ) )
    def and_(p: nf.Pattern, q: nf.Pattern) -> nf.Pattern:
        return neg(or_(neg(p), neg(q)))

    expected = and_(nf.MetaVar(10), nf.MetaVar(11))
    converted = scope.resolve_notation('\\and')(nf.MetaVar(10), nf.MetaVar(11))

    # \not \bot
    def top() -> nf.Pattern:
        return neg(bot())

    expected = top()
    converted = scope.resolve_notation('\\top')()
    assert expected == converted, pattern_mismatch(expected, converted)

    # \app \definedness ph0
    def ceil(p: nf.Pattern) -> nf.Pattern:
        return nf.Application(definedness, p)

    expected = ceil(nf.MetaVar(10))
    converted = scope.resolve_notation('\\ceil')(nf.MetaVar(10))
    assert expected == converted, pattern_mismatch(expected, converted)

    # \not ( \ceil ( \not ph0 ) )
    def floor(p: nf.Pattern) -> nf.Pattern:
        return neg(ceil(neg(p)))

    expected = floor(nf.MetaVar(10))
    converted = scope.resolve_notation('\\floor')(nf.MetaVar(10))
    assert expected == converted, pattern_mismatch(expected, converted)

    # \floor ( \imp ph0 ph1 )
    def included(p: nf.Pattern, q: nf.Pattern) -> nf.Pattern:
        return floor(nf.Implication(p, q))

    expected = included(nf.MetaVar(10), nf.MetaVar(11))
    converted = scope.resolve_notation('\\included')(nf.MetaVar(10), nf.MetaVar(11))
    assert expected == converted, pattern_mismatch(expected, converted)

    # \app \inhabitant ph0
    def inh(p: nf.Pattern) -> nf.Pattern:
        return nf.Application(inhabitant, p)

    expected = inh(nf.MetaVar(10))
    converted = scope.resolve_notation('\\inh')(nf.MetaVar(10))
    assert expected == converted, pattern_mismatch(expected, converted)

    # \included ph0 ( \inh ph1 )
    def in_sort(p: nf.Pattern, q: nf.Pattern) -> nf.Pattern:
        return included(p, inh(q))

    expected = in_sort(nf.MetaVar(10), nf.MetaVar(11))
    converted = scope.resolve_notation('\\in-sort')(nf.MetaVar(10), nf.MetaVar(11))
    assert expected == converted, pattern_mismatch(expected, converted)

    # \exists x ( \and ( \in-sort x ph0 ) ph1 )
    def sorted_exists(x: nf.Pattern, p: nf.Pattern, q: nf.Pattern) -> nf.Pattern:
        assert isinstance(x, nf.EVar)
        return nf.Exists(x, and_(in_sort(x, p), q))

    expected = sorted_exists(nf.EVar(10), nf.MetaVar(10), nf.MetaVar(11))
    converted = scope.resolve_notation('\\sorted-exists')(nf.EVar(10), nf.MetaVar(10), nf.MetaVar(11))
    assert expected == converted, pattern_mismatch(expected, converted)

    # TODO: Need a test for ambiguous notation
