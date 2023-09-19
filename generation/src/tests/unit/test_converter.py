from __future__ import annotations

import os
from typing import TYPE_CHECKING

import pytest

import proof_generation.pattern as nf
from mm_transfer.converter.converter import MetamathConverter
from mm_transfer.converter.representation import Axiom, AxiomWithAntecedents, Lemma, LemmaWithAntecedents
from mm_transfer.metamath.ast import ConstantStatement
from mm_transfer.metamath.parser import load_database

# from proof_generation.proof import BasicInterpreter, ExecutionPhase, StatefulInterpreter

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

    symbols = ('sg0', '\\definedness', '\\inhabitant', '\\tsymbol')
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
    converter = MetamathConverter(parsed_goal_database, parse_axioms=False)

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
    tst = scope._symbols['\\tsymbol']
    assert len(scope._notations) == 11 + 4  # from the file and builtin

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
    assert expected == converted, pattern_mismatch(expected, converted)

    #  \not ( \or ( \not ph0 ) ( \not ph1 ) )
    def and_(p: nf.Pattern, q: nf.Pattern) -> nf.Pattern:
        return neg(or_(neg(p), neg(q)))

    expected = and_(nf.MetaVar(10), nf.MetaVar(11))
    converted = scope.resolve_notation('\\and')(nf.MetaVar(10), nf.MetaVar(11))
    assert expected == converted, pattern_mismatch(expected, converted)

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

    # ( \tst xX )  = ( \tsymbol xX )
    def tste(x: nf.Pattern) -> nf.Pattern:
        assert isinstance(x, nf.EVar)
        return nf.Application(tst, x)

    def tsts(xs: nf.Pattern) -> nf.Pattern:
        assert isinstance(xs, nf.SVar)
        return nf.Application(tst, xs)

    expected = tste(nf.EVar(10))
    converted = scope.resolve_notation('\\tst', nf.EVar(10))(nf.EVar(10))
    assert expected == converted, pattern_mismatch(expected, converted)
    expected = tsts(nf.SVar(10))
    converted = scope.resolve_notation('\\tst', nf.SVar(10))(nf.SVar(10))
    assert expected == converted, pattern_mismatch(expected, converted)


def test_importing_simple_axioms(parsed_lemma_database: Database) -> None:
    converter = MetamathConverter(parsed_lemma_database)
    scope = converter._scope
    phi0 = converter._scope._metavars['ph0']
    phi1 = converter._scope._metavars['ph1']
    exx = converter._scope._element_vars['xX']
    sxx = converter._scope._set_vars['xX']
    tst = scope._symbols['\\tsymbol']
    and_ = scope.resolve_notation('\\and')

    # imp-reflexivity $a |- ( \imp ph0 ph0 ) $.
    expected = nf.Implication(phi0, phi0)
    assert 'imp-reflexivity' in converter._axioms and len(converter._axioms['imp-reflexivity']) == 1
    converted = converter._axioms['imp-reflexivity'][0].pattern
    assert expected == converted, pattern_mismatch(expected, converted)

    # and-elim-left-sugar $a |- ( \imp ( \and ph0 ph1 ) ph0 ) $.
    expected = nf.Implication(and_(phi0, phi1), phi0)
    assert 'and-elim-left-sugar' in converter._axioms and len(converter._axioms['and-elim-left-sugar']) == 1
    converted = converter._axioms['and-elim-left-sugar'][0].pattern
    assert expected == converted, pattern_mismatch(expected, converted)

    # and-elim-right-sugar $a |- ( \imp ( \and ph0 ph1 ) ph1 ) $.
    expected = nf.Implication(and_(phi0, phi1), phi1)
    assert 'and-elim-right-sugar' in converter._axioms and len(converter._axioms['and-elim-right-sugar']) == 1
    converted = converter._axioms['and-elim-right-sugar'][0].pattern
    assert expected == converted, pattern_mismatch(expected, converted)

    # tst-trivial-axiom $a |- ( \imp ( \tst xX ) ( \tst xX ) ) $.
    expected1 = nf.Implication(nf.Application(tst, exx), nf.Application(tst, exx))
    expected2 = nf.Implication(nf.Application(tst, sxx), nf.Application(tst, sxx))
    assert 'tst-trivial-axiom' in converter._axioms and len(converter._axioms['tst-trivial-axiom']) == 2
    converted1 = converter._axioms['tst-trivial-axiom'][0].pattern
    assert expected1 == converted1, pattern_mismatch(expected1, converted1)
    converted2 = converter._axioms['tst-trivial-axiom'][1].pattern
    assert expected2 == converted2, pattern_mismatch(expected2, converted2)


def test_axioms_with_mc(parsed_lemma_database: Database) -> None:
    converter = MetamathConverter(parsed_lemma_database)
    scope = converter._scope

    ph0 = converter._scope._metavars['ph0']
    ph1 = converter._scope._metavars['ph1']
    ph2 = converter._scope._metavars['ph2']
    converter._scope._metavars['ph3']
    converter._scope._metavars['ph4']
    ph5 = converter._scope._metavars['ph5']
    ph6 = converter._scope._metavars['ph6']
    x = converter._scope._element_vars['x']
    assert isinstance(x, nf.EVar)
    y = converter._scope._element_vars['y']
    assert isinstance(y, nf.EVar)
    and_ = scope.resolve_notation('\\and')
    sorted_exists_ = scope.resolve_notation('\\sorted-exists')
    in_sort_ = scope.resolve_notation('\\in-sort')
    top_ = scope.resolve_notation('\\top')

    # notation-proof
    name = 'notation-proof'
    antecedents: list[nf.Pattern] = [ph0]
    pattern = ph0
    assert name in converter._axioms and len(converter._axioms[name]) == 1
    converted = converter._axioms[name][0]
    assert isinstance(converted, AxiomWithAntecedents)
    assert len(converted.antecedents) == len(antecedents)
    assert antecedents[0] == converted.antecedents[0], pattern_mismatch(antecedents[0], converted.antecedents[0])
    assert pattern == converted.pattern, pattern_mismatch(pattern, converted.pattern)
    assert pattern == converter.get_axiom_by_name(name).pattern

    # proof-rule-gen
    name = 'proof-rule-gen'
    ph1_mc = nf.MetaVar(
        ph1.name,
        e_fresh=ph1.e_fresh + (x,),
        s_fresh=ph1.s_fresh,
        positive=ph1.positive,
        negative=ph1.negative,
        app_ctx_holes=ph1.app_ctx_holes,
    )
    antecedents = [nf.Implication(ph0, ph1_mc)]
    pattern = nf.Implication(nf.Exists(x, ph0), ph1_mc)
    assert name in converter._axioms and len(converter._axioms[name]) == 1
    converted = converter._axioms[name][0]
    assert isinstance(converted, AxiomWithAntecedents)
    assert len(converted.antecedents) == len(antecedents)
    assert antecedents[0] == converted.antecedents[0], pattern_mismatch(antecedents[0], converted.antecedents[0])
    assert pattern == converted.pattern, pattern_mismatch(pattern, converted.pattern)
    assert pattern == converter.get_axiom_by_name(name).pattern

    # rule-and-intro-alt2
    name = 'rule-and-intro-alt2-sugar'
    antecedents = [nf.Implication(ph0, ph1), nf.Implication(ph0, ph2)]
    pattern = nf.Implication(ph0, and_(ph1, ph2))
    assert name in converter._axioms and len(converter._axioms[name]) == 1
    converted = converter._axioms[name][0]
    assert isinstance(converted, AxiomWithAntecedents)
    assert len(converted.antecedents) == len(antecedents)
    for i in range(len(antecedents)):
        assert antecedents[i] == converted.antecedents[i], pattern_mismatch(antecedents[i], converted.antecedents[0])
    assert pattern == converted.pattern, pattern_mismatch(pattern, converted.pattern)
    assert pattern == converter.get_axiom_by_name(name).pattern

    # sorted-exists-propagation-converse
    name = 'sorted-exists-propagation-converse'
    antecedents = []
    ph0_mc = nf.MetaVar(
        ph0.name,
        e_fresh=ph0.e_fresh + (y,),
        s_fresh=ph0.s_fresh,
        positive=ph0.positive,
        negative=ph0.negative,
        app_ctx_holes=ph0.app_ctx_holes + (x,),
    )
    ph1_substututed = nf.ESubst(ph0_mc, x, ph5)
    evar = sorted_exists_(y, ph6, ph5)
    ph2_substututed = nf.ESubst(ph0_mc, x, evar)
    and_subpattern = and_(in_sort_(y, ph6), ph5)
    nf.ESubst(ph0_mc, x, and_subpattern)
    and_subpattern = and_(top_(), ph5)
    nf.ESubst(ph0_mc, x, and_subpattern)
    pattern = nf.Implication(sorted_exists_(y, ph6, ph1_substututed), ph2_substututed)
    assert name in converter._axioms and len(converter._axioms[name]) == 1
    converted = converter._axioms[name][0]
    assert isinstance(converted, Axiom) and not isinstance(converted, AxiomWithAntecedents)
    assert pattern == converted.pattern, pattern_mismatch(pattern, converted.pattern)


def test_lemma_with_mc(parsed_lemma_database: Database) -> None:
    converter = MetamathConverter(parsed_lemma_database)
    scope = converter._scope

    ph0 = converter._scope._metavars['ph0']
    ph1 = converter._scope._metavars['ph1']
    ph2 = converter._scope._metavars['ph2']
    x = converter._scope._element_vars['x']
    and_ = scope.resolve_notation('\\and')
    sorted_exists_ = scope.resolve_notation('\\sorted-exists')
    ceil_ = scope.resolve_notation('\\ceil')

    name = 'disjointness-alt-lemma'
    ph0_mc = nf.MetaVar(
        ph0.name,
        e_fresh=ph0.e_fresh + (x,),
        s_fresh=ph0.s_fresh,
        positive=ph0.positive,
        negative=ph0.negative,
        app_ctx_holes=ph0.app_ctx_holes,
    )
    # ( \imp ( \sorted-exists x ph2 ( \ceil ( \and ph0 ph1 ) ) ) ( \ceil ( \and ph0 ( \sorted-exists x ph2 ph1 ) ) ) )
    pattern = nf.Implication(
        sorted_exists_(x, ph2, ceil_(and_(ph0_mc, ph1))), ceil_(and_(ph0_mc, sorted_exists_(x, ph2, ph1)))
    )
    assert name in converter._lemmas and len(converter._lemmas[name]) == 1
    converted = converter._lemmas[name][0]
    assert isinstance(converted, Lemma) and not isinstance(converted, LemmaWithAntecedents)
    assert pattern == converted.pattern, pattern_mismatch(pattern, converted.pattern)
    assert pattern == converter.get_lemma_by_name(name).pattern
    assert converter.is_lemma(name)


def test_pattern_construction(parsed_lemma_database: Database) -> None:
    converter = MetamathConverter(parsed_lemma_database)
    scope = converter._scope
    assert len(converter.pattern_constructors) == 17

    ph0 = converter._scope._metavars['ph0']
    ph1 = converter._scope._metavars['ph1']
    x = converter._scope._element_vars['x']
    exx = converter._scope._element_vars['xX']
    sxx = converter._scope._set_vars['xX']
    tst = scope._symbols['\\tsymbol']
    inh_ = scope.resolve_notation('\\inh')
    sorted_exists_ = scope.resolve_notation('\\sorted-exists')

    # $a #Pattern ( \tst xX ) $.
    name = 'tst-is-pattern'
    expected1 = nf.Application(tst, exx)
    expected2 = nf.Application(tst, sxx)
    assert converter.is_pattern_constructor(name) and name in converter._axioms
    assert len(converter._axioms[name]) == 2
    converted1 = converter._axioms[name][0].pattern
    assert expected1 == converted1, pattern_mismatch(expected1, converted1)
    converted2 = converter._axioms[name][1].pattern
    assert expected2 == converted2, pattern_mismatch(expected2, converted2)

    # $a #Pattern ( \sorted-exists x ph0 ph1 ) $.
    name = 'sorted-exists-is-pattern'
    expected = sorted_exists_(x, ph0, ph1)
    assert converter.is_pattern_constructor(name) and name in converter._axioms
    assert len(converter._axioms[name]) == 1
    converted = converter._axioms[name][0].pattern
    assert expected == converted, pattern_mismatch(expected, converted)
    assert expected == converter.get_axiom_by_name(name).pattern

    # inh-is-pattern $a #Pattern ( \inh ph0 ) $.
    name = 'inh-is-pattern'
    expected = inh_(ph0)
    assert converter.is_pattern_constructor(name) and name in converter._axioms
    assert len(converter._axioms[name]) == 1
    converted = converter._axioms[name][0].pattern
    assert expected == converted, pattern_mismatch(expected, converted)
    assert expected == converter.get_axiom_by_name(name).pattern


def test_axiom_sorting(parsed_lemma_database: Database) -> None:
    converter = MetamathConverter(parsed_lemma_database)
    patterns = (
        'var-is-pattern',
        'symbol-is-pattern',
        'bot-is-pattern',
        'imp-is-pattern',
        'app-is-pattern',
        'exists-is-pattern',
        'not-is-pattern',
        'or-is-pattern',
        'and-is-pattern',
        'top-is-pattern',
        'ceil-is-pattern',
        'tst-is-pattern',
        'floor-is-pattern',
        'included-is-pattern',
        'inh-is-pattern',
        'in-sort-is-pattern',
        'sorted-exists-is-pattern',
    )
    assert converter.pattern_constructors == set(patterns)
    for pattern in patterns:
        assert converter.is_pattern_constructor(pattern)
    axioms = (
        'notation-proof',
        'tst-trivial-axiom',
        'imp-reflexivity',
        'rule-imp-transitivity',
        'and-elim-left-sugar',
        'and-elim-right-sugar',
        'rule-and-intro-alt2-sugar',
        'lemma-imp-compat-in-ceil',
        'lemma-imp-compat-in-exists',
        'sorted-exists-propagation-converse',
    )
    assert set(converter.exported_axioms) == set(axioms)
    for axiom in axioms:
        assert converter.is_exported_axiom(axiom)
    proof_rules = ('proof-rule-gen',)
    assert converter.proof_rules == set(proof_rules)
    for proof_rule in proof_rules:
        assert converter.is_proof_rule(proof_rule)

    for name in list(patterns) + list(axioms) + list(proof_rules):
        converter.is_axiom(name)


def test_interpreting_axioms(parsed_lemma_database: Database) -> None:
    # TODO: Enable the following tests
    pass
    # converter = MetamathConverter(parsed_lemma_database)

    # test using a basic interpreter
    # basic_interpreter = BasicInterpreter(phase=ExecutionPhase.Gamma)
    # converter.interpret_axioms(basic_interpreter)
    # # basic_interpreter object remains unchanged

    # # test using a stateful interpreter
    # state_interpreter = StatefulInterpreter(phase=ExecutionPhase.Gamma)
    # converter.interpret_axioms(state_interpreter)
    # expected = [a.pattern for a in converter.get_all_axioms()]
    # assert state_interpreter.stack == expected
