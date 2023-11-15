from __future__ import annotations

from itertools import count

from pytest import fixture, raises

from kore_transfer.kore_convertion.language_semantics import KModule, KSort, KSymbol, LanguageSemantics
from proof_generation.pattern import Pattern, Symbol
from proof_generation.proofs.kore import kore_rewrites


@fixture
def simple_semantics() -> LanguageSemantics:
    semantics = LanguageSemantics()
    with semantics as sem:
        mod = sem.module('test_module')
        with mod as mod:
            srt1 = mod.sort('srt1')
            srt2 = mod.sort('srt2')

            mod.symbol('sym1', srt1)
            mod.symbol('sym2', srt2, (srt1,), is_functional=True)
    return semantics


def test_module_creation() -> None:
    semantics = LanguageSemantics()
    with semantics as sem:
        with raises(ValueError):
            sem.main_module
        assert len(sem.modules) == 0

        test_name = 'test_module'
        m = sem.module(test_name)

        assert m.name == test_name
        assert len(sem.modules) == 1
        assert m in sem.modules


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
        with raises(ValueError):
            tr.sort('trivial_s')

        # It is forbidden to add hooked sorts with the same names as existing sorts
        with raises(ValueError):
            tr.hooked_sort('trivial_s')

        hookeds = tr.hooked_sort('trivial_hooked_s')
        assert hookeds in tr.sorts
        assert set(tr.sorts) == {ssort, hookeds}

        # It is forbidden to add sorts with the same names as existing hooked sorts
        with raises(ValueError):
            tr.sort('trivial_hooked_s')


def test_sorts() -> None:
    srt = KSort('srt')
    assert srt.name == 'srt'
    assert srt.aml_symbol == Symbol('ksort_srt')


def test_symbols() -> None:
    srt = KSort('srt')
    sym = KSymbol('sym', srt)
    assert sym.name == 'sym'
    assert sym.output_sort == srt
    assert sym.aml_symbol == Symbol('kore_sym')
    assert not sym.is_functional
    assert not sym.is_ctor
    assert not sym.is_cell


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
        with raises(ValueError):
            tr.symbol('bar', ssort)
        with raises(ValueError):
            tr.symbol('bar', KSort('Foo'))
        with raises(ValueError):
            tr.symbol('bar', KSort('Foo1'), is_functional=True)

        # It is forbidden to add symbols with unknown sorts
        with raises(ValueError):
            tr.symbol('bar', KSort('Foo1'))
        with raises(ValueError):
            tr.symbol('bar', ssort, (KSort('Foo'),), is_functional=True)

        # Testing setting symbol attributes
        fsymbol = tr.symbol('fbar', ssort, (ssort,), is_functional=True)
        assert fsymbol in tr.symbols
        assert set(tr.symbols) == {ssymbol, fsymbol}
        assert fsymbol.is_functional

        csymbol = tr.symbol('cbar', ssort, (ssort,), is_ctor=True)
        assert csymbol in tr.symbols
        assert csymbol.is_ctor

        cell_symbol = tr.symbol('cell', ssort, (ssort,), is_cell=True)
        assert cell_symbol in tr.symbols
        assert cell_symbol.is_cell

        # Testing getters for sorts and symbols
        assert trivial.get_sort('foo') == ssort
        assert trivial.get_symbol('bar') == ssymbol

        # Testing expected exception types
        with raises(ValueError):
            trivial.get_sort('unknown_sort')
        with raises(ValueError):
            trivial.get_symbol('unknown_symbol')


def test_module_import(simple_semantics: LanguageSemantics) -> None:
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

    # TODO: Creating a new modules separetly and importing it to the existing module
    # We expect it is to be tracked by semantics as it was added explicitly
    newest_module = KModule('newest_module', new_module.counter)
    with newest_module as nm:
        newest_sort = nm.sort('newest_module_srt')
        newest_symbol = nm.symbol('newest_module_sym', newest_sort)

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
    with raises(ValueError):
        simple_semantics.get_axiom(rule.ordinal + 1)
