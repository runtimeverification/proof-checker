from __future__ import annotations

from itertools import count

import pytest

from proof_generation.k.execution_proof_generation import ExecutionProofExp
from proof_generation.k.kore_convertion.language_semantics import KModule, KSort, KSortVar, KSymbol, LanguageSemantics
from proof_generation.pattern import EVar, Pattern, Symbol, phi0, phi1
from proof_generation.proofs.definedness import ceil, equals, floor, functional, subset
from proof_generation.proofs.kore import KORE_NOTATIONS, KoreLemmas, kore_rewrites, nary_app
from proof_generation.proofs.propositional import PROPOSITIONAL_NOTATIONS


@pytest.fixture
def simple_semantics() -> LanguageSemantics:
    semantics = LanguageSemantics()
    with semantics as sem:
        mod = sem.module('test_module')
        with mod as mod:
            srt1 = mod.sort('srt1')
            srt2 = mod.sort('srt2')

            mod.symbol('sym1', srt1)
            mod.symbol('sym2', srt2, input_sorts=(srt1,), is_functional=True)
    return semantics


def test_module_creation() -> None:
    semantics = LanguageSemantics()
    with semantics as sem:
        with pytest.raises(ValueError):
            sem.main_module
        assert len(sem.modules) == 0

        test_name = 'test_module'
        m = sem.module(test_name)

        assert m.name == test_name
        assert len(sem.modules) == 1
        assert m in sem.modules


def test_language_semantics_notations(simple_semantics: LanguageSemantics) -> None:
    expected_notations = {
        *set(KORE_NOTATIONS),
        *set(PROPOSITIONAL_NOTATIONS),
        *{s.aml_notation for s in simple_semantics.main_module.symbols},
    }

    assert isinstance(simple_semantics.notations, tuple)
    assert set(simple_semantics.notations) == expected_notations


def test_module_sort() -> None:
    trivial = KModule('trivial', count())
    with trivial as tr:
        assert tr.sorts == (), 'Expect no initial sorts'

        # Add a sort
        ssort = tr.sort('trivial_s')
        assert isinstance(ssort, KSort), f'Expect a sort object, got {str(ssort)}'
        assert ssort in tr.sorts
        assert len(tr.sorts) == 1

        # It is forbidden to add sorts twice
        with pytest.raises(ValueError):
            tr.sort('trivial_s')

        # It is forbidden to add hooked sorts with the same names as existing sorts
        with pytest.raises(ValueError):
            tr.hooked_sort('trivial_s')

        hookeds = tr.hooked_sort('trivial_hooked_s')
        assert hookeds in tr.sorts
        assert set(tr.sorts) == {ssort, hookeds}

        # It is forbidden to add sorts with the same names as existing hooked sorts
        with pytest.raises(ValueError):
            tr.sort('trivial_hooked_s')


def test_sorts() -> None:
    srt = KSort('srt')
    assert srt.name == 'srt'
    assert srt.aml_symbol == Symbol('ksort_srt')


def test_symbols() -> None:
    # Test the basic case
    srt1 = KSort('srt1')
    sym = KSymbol('sym', (), srt1)
    assert sym.name == 'sym'
    assert sym.output_sort == srt1
    assert sym.aml_symbol == Symbol('kore_sym')
    assert not sym.is_functional
    assert not sym.is_ctor
    assert not sym.is_cell
    # This is an intentionally strict comparison that also checks that
    # nary_app caching working and it does work even with different
    # equivalent instances of the Symbol class
    # The rest comparisons will be just equality checks
    assert sym.aml_notation is nary_app(Symbol(sym.aml_symbol.name), 0, False)

    # Test the creation of a functional symbol
    srt2 = KSort('srt2')
    fsym = KSymbol('fsym', (), srt1, (srt1, srt2), is_functional=True)
    assert fsym.name == 'fsym'
    assert fsym.output_sort == srt1
    assert fsym.input_sorts == (srt1, srt2)
    assert fsym.aml_symbol == Symbol('kore_fsym')
    assert fsym.is_functional
    assert not fsym.is_ctor
    assert not fsym.is_cell
    assert fsym.aml_notation == nary_app(fsym.aml_symbol, 2, False)

    # Test the usage of flags
    csym = KSymbol('csym', (), srt1, (srt1, srt2), is_ctor=True)
    assert not csym.is_functional
    assert csym.is_ctor
    assert not csym.is_cell

    # Test the creation of a cell
    cell_sym = KSymbol('cell', (), srt1, (srt1, srt2), is_functional=True, is_cell=True)
    assert cell_sym.name == 'cell'
    assert cell_sym.output_sort == srt1
    assert cell_sym.input_sorts == (srt1, srt2)
    assert cell_sym.aml_symbol == Symbol('kore_cell')
    assert cell_sym.is_functional
    assert not cell_sym.is_ctor
    assert cell_sym.is_cell
    assert cell_sym.aml_notation == nary_app(cell_sym.aml_symbol, 2, True)


def test_symbol_params() -> None:
    sort1 = KSort('sort1')
    sort2 = KSortVar('var1')
    sort3 = KSortVar('var2')

    symbol1 = KSymbol('symbol1', (), sort1)
    assert symbol1.input_sorts == ()
    assert symbol1.sort_params == ()
    assert symbol1.aml_symbol == Symbol('kore_symbol1')
    assert symbol1.aml_notation == nary_app(Symbol('kore_symbol1'), 0, False)

    symbol2 = KSymbol('symbol2', (sort2,), sort1, (sort1, sort2))
    assert symbol2.input_sorts == (sort1, sort2)
    assert symbol2.sort_params == (sort2,)
    assert symbol2.aml_symbol == Symbol('kore_symbol2')
    assert symbol2.aml_notation == nary_app(Symbol('kore_symbol2'), 3, False)

    symbol3 = KSymbol('symbol3', (sort2, sort3), sort3, (sort1, sort2), is_functional=True)
    assert symbol3.input_sorts == (sort1, sort2)
    assert symbol3.sort_params == (sort2, sort3)
    assert symbol3.aml_symbol == Symbol('kore_symbol3')
    assert symbol3.aml_notation == nary_app(Symbol('kore_symbol3'), 4, False)

    symbol3 = KSymbol('symbol3', (sort2, sort3), sort3, (sort1, sort2, sort2), is_functional=True, is_cell=True)
    assert symbol3.input_sorts == (sort1, sort2, sort2)
    assert symbol3.sort_params == (sort2, sort3)
    assert symbol3.aml_symbol == Symbol('kore_symbol3')
    assert symbol3.aml_notation == nary_app(Symbol('kore_symbol3'), 5, True)


def test_module_symbols() -> None:
    trivial = KModule('trivial', count())
    with trivial as tr:
        assert tr.symbols == (), 'Expect no initial symbols'

        # Add a symbol
        ssort = tr.sort('foo')
        ssymbol = tr.symbol('bar', ssort)
        assert isinstance(ssymbol, KSymbol), f'Expect a symbol object, got {str(ssort)}'
        assert ssymbol in tr.symbols, 'Expect the symbol to be in the module'
        assert len(tr.symbols) == 1, 'Expect the only symbol in the module'

        # It is forbidden to add symbols twice
        with pytest.raises(ValueError):
            tr.symbol('bar', ssort)
        with pytest.raises(ValueError):
            tr.symbol('bar', KSort('Foo'))
        with pytest.raises(ValueError):
            tr.symbol('bar', KSort('Foo1'), is_functional=True)

        # It is forbidden to add symbols with unknown sorts
        with pytest.raises(ValueError):
            tr.symbol('bar', KSort('Foo1'))
        with pytest.raises(ValueError):
            tr.symbol('bar', ssort, input_sorts=(KSort('Foo'),), is_functional=True)

        # Testing setting symbol attributes
        fsymbol = tr.symbol('fbar', ssort, input_sorts=(ssort,), is_functional=True)
        assert fsymbol in tr.symbols
        assert set(tr.symbols) == {ssymbol, fsymbol}
        assert fsymbol.is_functional

        csymbol = tr.symbol('cbar', ssort, input_sorts=(ssort,), is_ctor=True)
        assert csymbol in tr.symbols
        assert csymbol.is_ctor

        cell_symbol = tr.symbol('cell', ssort, input_sorts=(ssort,), is_cell=True)
        assert cell_symbol in tr.symbols
        assert cell_symbol.is_cell

        param_sort = KSortVar('param')
        param_symbol = tr.symbol('param', ssort, sort_params=(param_sort,), input_sorts=(param_sort,))
        assert param_symbol in tr.symbols
        assert param_symbol.sort_params == (param_sort,)
        assert param_symbol.input_sorts == (param_sort,)

        # Testing getters for sorts and symbols
        assert trivial.get_sort('foo') == ssort
        assert trivial.get_symbol('bar') == ssymbol

        # Testing expected exception types
        with pytest.raises(ValueError):
            trivial.get_sort('unknown_sort')
        with pytest.raises(ValueError):
            trivial.get_symbol('unknown_symbol')


def test_module_import(simple_semantics: LanguageSemantics) -> None:
    ever_created_sorts = set(simple_semantics.main_module.sorts)
    ever_created_symbols = set(simple_semantics.main_module.symbols)
    initial_sorts = set(simple_semantics.main_module.sorts)
    initial_symbols = set(simple_semantics.main_module.symbols)

    # Testing expected initial semantics setup
    assert len(simple_semantics.modules) == 1, 'Expect one module'
    assert simple_semantics.main_module.name == 'test_module'
    old_module = simple_semantics.main_module

    # Adding a new module and importing it to the existing one
    added_symbol = None
    added_sort = None
    with simple_semantics as sem:
        new_module = sem.module('new_module')

        # Populate the new module
        with new_module as nm:
            added_sort = nm.sort('new_module_srt')
            added_symbol = nm.symbol('new_module_sym', added_sort)
            ever_created_sorts.add(added_sort)
            ever_created_symbols.add(added_symbol)

    # Expect the counter to be inherited
    assert new_module.counter == old_module.counter

    # Check that the new module is added to the semantics
    assert set(simple_semantics.modules) == {new_module, old_module}
    assert simple_semantics.main_module == new_module
    assert simple_semantics.get_module('new_module') == new_module

    # Check that the content of the new module is available in the semantics
    assert added_symbol == simple_semantics.get_symbol('new_module_sym') is not None
    assert added_sort == simple_semantics.get_sort('new_module_srt') is not None
    assert added_symbol == simple_semantics.get_symbol('new_module_sym') is not None
    assert added_sort == simple_semantics.get_sort('new_module_srt') is not None

    # Check that all symbols and sorts are collected recursievly
    assert set(simple_semantics.sorts) == ever_created_sorts
    assert set(simple_semantics.symbols) == ever_created_symbols
    assert set(old_module.sorts) == initial_sorts
    assert set(old_module.symbols) == initial_symbols
    assert set(new_module.sorts) == {added_sort}
    assert set(new_module.symbols) == {added_symbol}

    # TODO: Creating a new modules separetly and importing it to the existing module
    # We expect it is to be tracked by semantics as it was added explicitly
    newest_module = KModule('newest_module', new_module.counter)
    with newest_module as nm:
        newest_sort = nm.sort('newest_module_srt')
        newest_symbol = nm.symbol('newest_module_sym', newest_sort)
        ever_created_sorts.add(newest_sort)
        ever_created_symbols.add(newest_symbol)

        pattern = kore_rewrites(newest_sort.aml_symbol, newest_symbol.aml_symbol, newest_symbol.aml_symbol)
        assert isinstance(pattern, Pattern)
        rule = nm.rewrite_rule(pattern)
    with simple_semantics.main_module as mm:
        mm.import_module(newest_module)

    # Test that the new module is available in the semantics
    assert newest_module in simple_semantics.modules
    assert set(simple_semantics.modules) == {old_module, new_module, newest_module}
    assert simple_semantics.get_module('newest_module') == newest_module

    # Test that the content is gettable
    assert simple_semantics.get_symbol('newest_module_sym') is newest_symbol
    assert simple_semantics.get_sort('newest_module_srt') is newest_sort
    assert simple_semantics.main_module.get_symbol('newest_module_sym') is newest_symbol
    assert simple_semantics.main_module.get_sort('newest_module_srt') is newest_sort

    # Test accessing added rule
    assert newest_module.get_axiom(rule.ordinal) == rule
    assert simple_semantics.main_module.get_axiom(rule.ordinal) == rule
    assert simple_semantics.get_axiom(rule.ordinal) == rule
    with pytest.raises(ValueError):
        simple_semantics.get_axiom(rule.ordinal + 1)

    # Test final sets of sorts, symbols and notations
    assert set(simple_semantics.sorts) == ever_created_sorts
    assert set(simple_semantics.symbols) == ever_created_symbols
    assert set(old_module.sorts) == initial_sorts
    assert set(old_module.symbols) == initial_symbols
    assert set(new_module.sorts) == {added_sort, newest_sort}
    assert set(new_module.symbols) == {added_symbol, newest_symbol}
    assert set(newest_module.sorts) == {newest_sort}
    assert set(newest_module.symbols) == {newest_symbol}

    # Test that semantics notations are updated
    assert set(simple_semantics.notations) == {
        *set(KORE_NOTATIONS),
        *set(PROPOSITIONAL_NOTATIONS),
        *{s.aml_notation for s in ever_created_symbols},
    }


def test_collect_functional_axioms() -> None:
    semantics = LanguageSemantics()
    with semantics as sem:
        module = sem.module('test')
        with module as mod:
            sort = mod.sort('sort')
            a_symbol = mod.symbol('a', sort, input_sorts=(sort,), is_functional=True, is_ctor=True)
            b_symbol = mod.symbol('b', sort, input_sorts=(), is_functional=True, is_ctor=True)
            c_symbol = mod.symbol('c', sort, input_sorts=(sort,), is_functional=True, is_ctor=True)
            d_symbol = mod.symbol('d', sort, input_sorts=(sort, sort), is_functional=True, is_ctor=True)
            a = a_symbol.aml_notation
            b = b_symbol.aml_symbol
            c = c_symbol.aml_notation
            d = d_symbol.aml_notation
            single_evar_krule = kore_rewrites(sort.aml_symbol, EVar(0), EVar(0))
            double_evar_krule = kore_rewrites(sort.aml_symbol, d(EVar(0), EVar(1)), d(EVar(0), EVar(1)))

            b_pe = ExecutionProofExp(sem, b)
            b_pe.rewrite_event(
                single_evar_krule,
                {0: b},
            )
            assert functional(b) in b_pe.get_axioms()

            ab_pe = ExecutionProofExp(sem, a(b))
            ab_pe.rewrite_event(
                single_evar_krule,
                {0: a(b)},
            )
            assert functional(a(b)) in ab_pe.get_axioms()

            cbb_pe = ExecutionProofExp(sem, d(c(b), b))
            cbb_pe.rewrite_event(
                double_evar_krule,
                {0: a(b), 1: b},
            )
            assert functional(c(b)) in cbb_pe.get_axioms()
            assert functional(b) in cbb_pe.get_axioms()


@pytest.mark.parametrize(
    'pat, pretty_pat',
    [
        (ceil(phi0), '⌈ phi0 ⌉'),
        (floor(phi0), '⌊ phi0 ⌋'),
        (subset(phi0, phi1), '(phi0 ⊆ phi1)'),
        (equals(phi0, phi1), '(phi0 = phi1)'),
        (functional(phi0), 'functional(phi0)'),
    ],
)
def test_pretty_print_functional_axioms(pat: Pattern, pretty_pat: str) -> None:
    pretty_opt = KoreLemmas().pretty_options()
    assert pat.pretty(pretty_opt) == pretty_pat
