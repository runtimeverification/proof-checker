from __future__ import annotations

import os
from typing import TYPE_CHECKING

import pytest

from proof_generation.metamath.ast import AxiomaticStatement, Block, ConstantStatement, FloatingStatement
from proof_generation.metamath.converter.converter import MetamathConverter
from proof_generation.metamath.converter.representation import Axiom, AxiomWithAntecedents, Lemma, LemmaWithAntecedents
from proof_generation.metamath.parser import load_database
from proof_generation.pattern import App, ESubst, EVar, Exists, Implies, MetaVar, SVar, Symbol

if TYPE_CHECKING:
    from proof_generation.metamath.ast import Database
    from proof_generation.pattern import Pattern

BENCHMARK_LOCATION = 'generation/mm-benchmarks'


@pytest.fixture
def parsed_lemma_database() -> Database:
    return load_database(os.path.join(BENCHMARK_LOCATION, 'disjointness-alt-lemma.mm'), include_proof=True)


@pytest.fixture
def parsed_goal_database() -> Database:
    return load_database(os.path.join(BENCHMARK_LOCATION, 'transfer-goal.mm'), include_proof=True)


@pytest.fixture
def parsed_perceptron_goal_database() -> Database:
    return load_database(os.path.join(BENCHMARK_LOCATION, 'perceptron-goal.mm'), include_proof=True)


@pytest.fixture
def parsed_svm5_goal_database() -> Database:
    return load_database(os.path.join(BENCHMARK_LOCATION, 'svm5-goal.mm'), include_proof=True)


@pytest.fixture
def parsed_impreflex_database() -> Database:
    return load_database(os.path.join(BENCHMARK_LOCATION, 'impreflex.mm'), include_proof=True)


def pattern_mismatch(p1: Pattern, p2: Pattern) -> str:
    return f'Pattern mismatch: {str(p1)} != {str(p2)}'


def test_importing_variables(parsed_lemma_database: Database) -> None:
    converter = MetamathConverter(parsed_lemma_database)

    patterns = ('ph0', 'ph1', 'ph2', 'ph3', 'ph4', 'ph5', 'ph6')
    for pattern in patterns:
        assert pattern in converter._scope._metavars
    assert len(converter._scope._metavars) == len(patterns)

    symbols = ('sg0', '\\definedness', '\\inhabitant', '\\tsymbol', '\\tapp')
    for symbol in symbols:
        assert symbol in converter._symbols
    assert len(converter._symbols) == len(symbols) + 1  # +1 is given by an undefined \and

    evars = ('x', 'y', 'xX')
    for evar in evars:
        assert evar in converter._scope._element_vars
    assert len(converter._scope._element_vars) == len(evars)

    setvars = ('X', 'xX')
    for setvar in setvars:
        assert setvar in converter._scope._set_vars
    assert len(converter._scope._set_vars) == len(setvars)

    # Check that all labels are accessible
    floating_statements = filter(
        lambda statement: isinstance(statement, FloatingStatement), parsed_lemma_database.statements
    )
    for statement in floating_statements:
        assert isinstance(statement, FloatingStatement)
        assert converter.get_floating_pattern_by_name(statement.label) is not None


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
    assert converter._domain_values == set(domain_values)


def test_importing_notations(parsed_lemma_database: Database) -> None:
    converter = MetamathConverter(parsed_lemma_database)
    scope = converter._scope
    definedness = converter._symbols['\\definedness']
    inhabitant = converter._symbols['\\inhabitant']
    tst = converter._symbols['\\tsymbol']
    assert len(scope._notations) == 11 + 4  # from the file and builtin

    def bot() -> Pattern:
        return Symbol('\\bot')

    # bot does not have a definition, so it is treated as a logical symbol
    expected = bot()
    converted = converter._symbols['\\bot']
    assert expected == converted, pattern_mismatch(expected, converted)

    def neg(p: Pattern) -> Pattern:
        return Implies(p, bot())

    expected = neg(MetaVar(10))
    converted = scope.resolve_notation('\\not')(MetaVar(10))
    assert expected == converted, pattern_mismatch(expected, converted)

    # \imp ( \not ph0 ) ph1
    def or_(p: Pattern, q: Pattern) -> Pattern:
        return Implies(neg(p), q)

    expected = or_(MetaVar(10), MetaVar(11))
    converted = scope.resolve_notation('\\or')(MetaVar(10), MetaVar(11))
    assert expected == converted, pattern_mismatch(expected, converted)

    #  \not ( \or ( \not ph0 ) ( \not ph1 ) )
    def and_(p: Pattern, q: Pattern) -> Pattern:
        return neg(or_(neg(p), neg(q)))

    expected = and_(MetaVar(10), MetaVar(11))
    converted = scope.resolve_notation('\\and')(MetaVar(10), MetaVar(11))
    assert expected == converted, pattern_mismatch(expected, converted)

    # \not \bot
    def top() -> Pattern:
        return neg(bot())

    expected = top()
    converted = scope.resolve_notation('\\top')()
    assert expected == converted, pattern_mismatch(expected, converted)

    # \app \definedness ph0
    def ceil(p: Pattern) -> Pattern:
        return App(definedness, p)

    expected = ceil(MetaVar(10))
    converted = scope.resolve_notation('\\ceil')(MetaVar(10))
    assert expected == converted, pattern_mismatch(expected, converted)

    # \not ( \ceil ( \not ph0 ) )
    def floor(p: Pattern) -> Pattern:
        return neg(ceil(neg(p)))

    expected = floor(MetaVar(10))
    converted = scope.resolve_notation('\\floor')(MetaVar(10))
    assert expected == converted, pattern_mismatch(expected, converted)

    # \floor ( \imp ph0 ph1 )
    def included(p: Pattern, q: Pattern) -> Pattern:
        return floor(Implies(p, q))

    expected = included(MetaVar(10), MetaVar(11))
    converted = scope.resolve_notation('\\included')(MetaVar(10), MetaVar(11))
    assert expected == converted, pattern_mismatch(expected, converted)

    # \app \inhabitant ph0
    def inh(p: Pattern) -> Pattern:
        return App(inhabitant, p)

    expected = inh(MetaVar(10))
    converted = scope.resolve_notation('\\inh')(MetaVar(10))
    assert expected == converted, pattern_mismatch(expected, converted)

    # \included ph0 ( \inh ph1 )
    def in_sort(p: Pattern, q: Pattern) -> Pattern:
        return included(p, inh(q))

    expected = in_sort(MetaVar(10), MetaVar(11))
    converted = scope.resolve_notation('\\in-sort')(MetaVar(10), MetaVar(11))
    assert expected == converted, pattern_mismatch(expected, converted)

    # \exists x ( \and ( \in-sort x ph0 ) ph1 )
    def sorted_exists(x: Pattern, p: Pattern, q: Pattern) -> Pattern:
        assert isinstance(x, EVar)
        return Exists(x.name, and_(in_sort(x, p), q))

    expected = sorted_exists(EVar(10), MetaVar(10), MetaVar(11))
    converted = scope.resolve_notation('\\sorted-exists')(EVar(10), MetaVar(10), MetaVar(11))
    assert expected == converted, pattern_mismatch(expected, converted)

    # ( \tst xX )  = ( \tsymbol xX )
    def tste(x: Pattern) -> Pattern:
        assert isinstance(x, EVar)
        return App(tst, x)

    def tsts(xs: Pattern) -> Pattern:
        assert isinstance(xs, SVar)
        return App(tst, xs)

    expected = tste(EVar(10))
    converted = scope.resolve_notation('\\tst', EVar(10))(EVar(10))
    assert expected == converted, pattern_mismatch(expected, converted)
    expected = tsts(SVar(10))
    converted = scope.resolve_notation('\\tst', SVar(10))(SVar(10))
    assert expected == converted, pattern_mismatch(expected, converted)


def test_importing_simple_axioms(parsed_lemma_database: Database) -> None:
    converter = MetamathConverter(parsed_lemma_database)
    scope = converter._scope
    phi0 = converter._scope._metavars['ph0']
    phi1 = converter._scope._metavars['ph1']
    x = converter._scope._element_vars['x']
    y = converter._scope._element_vars['y']
    exx = converter._scope._element_vars['xX']
    sxx = converter._scope._set_vars['xX']
    tst = converter._symbols['\\tsymbol']
    tapp = converter._symbols['\\tapp']
    and_ = scope.resolve_notation('\\and')

    # imp-reflexivity $a |- ( \imp ph0 ph0 ) $.
    expected = Implies(phi0, phi0)
    assert 'imp-reflexivity' in converter._axioms and len(converter._axioms['imp-reflexivity']) == 1
    converted = converter._axioms['imp-reflexivity'][0].pattern
    assert expected == converted, pattern_mismatch(expected, converted)

    # and-elim-left-sugar $a |- ( \imp ( \and ph0 ph1 ) ph0 ) $.
    expected = Implies(and_(phi0, phi1), phi0)
    assert 'and-elim-left-sugar' in converter._axioms and len(converter._axioms['and-elim-left-sugar']) == 1
    converted = converter._axioms['and-elim-left-sugar'][0].pattern
    assert expected == converted, pattern_mismatch(expected, converted)

    # and-elim-right-sugar $a |- ( \imp ( \and ph0 ph1 ) ph1 ) $.
    expected = Implies(and_(phi0, phi1), phi1)
    assert 'and-elim-right-sugar' in converter._axioms and len(converter._axioms['and-elim-right-sugar']) == 1
    converted = converter._axioms['and-elim-right-sugar'][0].pattern
    assert expected == converted, pattern_mismatch(expected, converted)

    # tst-trivial-axiom $a |- ( \imp ( \tst xX ) ( \tst xX ) ) $.
    expected1 = Implies(App(tst, exx), App(tst, exx))
    expected2 = Implies(App(tst, sxx), App(tst, sxx))
    assert 'tst-trivial-axiom' in converter._axioms and len(converter._axioms['tst-trivial-axiom']) == 2
    converted1 = converter._axioms['tst-trivial-axiom'][0].pattern
    assert expected1 == converted1, pattern_mismatch(expected1, converted1)
    converted2 = converter._axioms['tst-trivial-axiom'][1].pattern
    assert expected2 == converted2, pattern_mismatch(expected2, converted2)

    # tst-missing-axiom $a |- ( \imp ( \tst x ) ( \tapp x y ) ) $.
    expected = Implies(App(tst, x), App(App(tapp, x), y))
    assert 'tst-missing-symbol-axiom' in converter._axioms and len(converter._axioms['tst-missing-symbol-axiom']) == 1
    converted = converter._axioms['tst-missing-symbol-axiom'][0].pattern
    assert expected == converted, pattern_mismatch(expected, converted)


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
    assert isinstance(x, EVar)
    y = converter._scope._element_vars['y']
    assert isinstance(y, EVar)
    and_ = scope.resolve_notation('\\and')
    sorted_exists_ = scope.resolve_notation('\\sorted-exists')
    in_sort_ = scope.resolve_notation('\\in-sort')
    top_ = scope.resolve_notation('\\top')

    # notation-proof
    name = 'notation-proof'
    antecedents: list[Pattern] = [ph0]
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
    ph1_mc = MetaVar(
        ph1.name,
        e_fresh=ph1.e_fresh + (x,),
        s_fresh=ph1.s_fresh,
        positive=ph1.positive,
        negative=ph1.negative,
        app_ctx_holes=ph1.app_ctx_holes,
    )
    antecedents = [Implies(ph0, ph1_mc)]
    pattern = Implies(Exists(x.name, ph0), ph1_mc)
    assert name in converter._axioms and len(converter._axioms[name]) == 1
    converted = converter._axioms[name][0]
    assert isinstance(converted, AxiomWithAntecedents)
    assert len(converted.antecedents) == len(antecedents)
    assert antecedents[0] == converted.antecedents[0], pattern_mismatch(antecedents[0], converted.antecedents[0])
    assert pattern == converted.pattern, pattern_mismatch(pattern, converted.pattern)
    assert pattern == converter.get_axiom_by_name(name).pattern

    # rule-and-intro-alt2
    name = 'rule-and-intro-alt2-sugar'
    antecedents = [Implies(ph0, ph1), Implies(ph0, ph2)]
    pattern = Implies(ph0, and_(ph1, ph2))
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
    ph0_mc = MetaVar(
        ph0.name,
        e_fresh=ph0.e_fresh + (y,),
        s_fresh=ph0.s_fresh,
        positive=ph0.positive,
        negative=ph0.negative,
        app_ctx_holes=ph0.app_ctx_holes + (x,),
    )
    ph1_substututed = ESubst(ph0_mc, x, ph5)
    evar = sorted_exists_(y, ph6, ph5)
    ph2_substututed = ESubst(ph0_mc, x, evar)
    and_subpattern = and_(in_sort_(y, ph6), ph5)
    ESubst(ph0_mc, x, and_subpattern)
    and_subpattern = and_(top_(), ph5)
    ESubst(ph0_mc, x, and_subpattern)
    pattern = Implies(sorted_exists_(y, ph6, ph1_substututed), ph2_substututed)
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
    ph0_mc = MetaVar(
        ph0.name,
        e_fresh=ph0.e_fresh + (x,),
        s_fresh=ph0.s_fresh,
        positive=ph0.positive,
        negative=ph0.negative,
        app_ctx_holes=ph0.app_ctx_holes,
    )
    # ( \imp ( \sorted-exists x ph2 ( \ceil ( \and ph0 ph1 ) ) ) ( \ceil ( \and ph0 ( \sorted-exists x ph2 ph1 ) ) ) )
    pattern = Implies(
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
    assert len(converter.pattern_constructors) == 32

    ph0 = converter._scope._metavars['ph0']
    ph1 = converter._scope._metavars['ph1']
    x = converter._scope._element_vars['x']
    exx = converter._scope._element_vars['xX']
    sxx = converter._scope._set_vars['xX']
    tst = converter._symbols['\\tsymbol']
    inh_ = scope.resolve_notation('\\inh')
    sorted_exists_ = scope.resolve_notation('\\sorted-exists')

    # $a #Pattern ( \tst xX ) $.
    name = 'tst-is-pattern'
    expected1 = App(tst, exx)
    expected2 = App(tst, sxx)
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
        'included-is-sugar',
        'ceil-is-sugar',
        'floor-is-sugar',
        'tsymbol-is-symbol',
        'in-sort-is-sugar',
        'not-is-sugar',
        'element-var-is-var',
        'and-is-sugar',
        'inh-is-sugar',
        'tst-is-sugar',
        'or-is-sugar',
        'inhabitant-is-symbol',
        'top-is-sugar',
        'definedness-is-symbol',
        'sorted-exists-is-sugar',
        'definedness-is-symbol',
    )
    assert converter.pattern_constructors == set(patterns)
    for pattern in patterns:
        assert converter.is_pattern_constructor(pattern)
    axioms = (
        'notation-proof',
        'tst-trivial-axiom',
        'tst-missing-symbol-axiom',
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

    assert converter.get_metavars_in_order('proof-rule-gen') == ('ph0', 'ph1')
    assert converter.get_metavars_in_order('disjointness-alt-lemma') == ('ph0', 'ph1', 'ph2')

    assert converter.resolve_metavar('ph1') == converter._scope._metavars['ph1']
    assert converter.get_metavar_name_by_label('ph1-is-pattern') == converter._scope._metavars['ph1']


def test_transfer_goal_axioms_resolving(parsed_goal_database: Database) -> None:
    converter = MetamathConverter(parsed_goal_database)

    # Collect all axiom labels in a tuple or set
    axiom_labels: list[str] = []
    axiomatic_statements = list(
        filter(lambda statement: isinstance(statement, AxiomaticStatement | Block), parsed_goal_database.statements)
    )
    for statement in axiomatic_statements:
        if isinstance(statement, AxiomaticStatement):
            axiom_labels.append(statement.label)
        elif isinstance(statement, Block) and isinstance(statement.statements[-1], AxiomaticStatement):
            axiom_labels.append(statement.statements[-1].label)
        else:
            continue

    # Check that all axioms are resolved
    for axiom_label in axiom_labels:
        assert converter.is_axiom(axiom_label)
        assert converter.get_axiom_by_name(axiom_label) is not None


def test_converting_perceptron_goal(parsed_perceptron_goal_database: Database) -> None:
    converter = MetamathConverter(parsed_perceptron_goal_database)
    assert set(converter._lemmas.keys()) == {'goal'}
    assert len(converter._axioms) == 95


def test_converting_svm_goal(parsed_svm5_goal_database: Database) -> None:
    converter = MetamathConverter(parsed_svm5_goal_database)
    assert set(converter._lemmas.keys()) == {'goal'}
    assert len(converter._axioms) == 95


def test_parsing_proof(parsed_impreflex_database: Database) -> None:
    converter = MetamathConverter(parsed_impreflex_database)
    assert set(converter._lemmas.keys()) == {'imp-reflexivity'}
    assert len(converter._axioms) == 4

    assert converter._lemmas['imp-reflexivity'][0].proof.labels == {
        1: 'ph0-is-pattern',
        2: 'imp-is-pattern',
        3: 'proof-rule-prop-1',
        4: 'proof-rule-mp',
        5: 'proof-rule-prop-2',
    }

    assert converter._lemmas['imp-reflexivity'][0].proof.applied_lemmas == [
        1,
        1,
        1,
        2,
        2,
        1,
        1,
        2,
        1,
        1,
        1,
        2,
        1,
        2,
        2,
        1,
        1,
        1,
        2,
        2,
        1,
        1,
        2,
        2,
        1,
        1,
        1,
        2,
        1,
        5,
        1,
        1,
        1,
        2,
        3,
        4,
        1,
        1,
        3,
        4,
    ]
