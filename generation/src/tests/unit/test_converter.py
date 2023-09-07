from __future__ import annotations

import os
from typing import TYPE_CHECKING

import pytest

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


def test_importing_variables(parsed_lemma_database: Database) -> None:
    converter = MetamathConverter(parsed_lemma_database)

    patterns = ('ph0', 'ph1', 'ph2', 'ph3', 'ph4', 'ph5', 'ph6', 'xX')
    for pattern in patterns:
        assert pattern in converter._scope._metavars
    assert len(converter._scope._metavars) == len(patterns)

    symbols = ('sg0',)
    for symbol in symbols:
        assert symbol in converter._scope._symbols
    assert len(converter._scope._symbols) == len(symbols)

    evars = ('x', 'y')
    for evar in evars:
        assert evar in converter._scope._element_vars
    assert len(converter._scope._element_vars) == len(evars)

    setvars = ('X',)
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


def test_importing_notations(parsed_lemma_database):
    converter = MetamathConverter(parsed_lemma_database)
    assert len(converter._notations) == 10
    raise NotImplementedError
