from __future__ import annotations

from itertools import count

from pytest import raises

from kore_transfer.language_definition import KModule, KSort, KSymbol, LanguageSemantics


def test_module_creation() -> None:
    semantics = LanguageSemantics()
    with semantics as definition:
        test_name = 'test_module'
        m = definition.module(test_name)

        assert m.name == test_name
        assert len(definition.modules) == 1
        assert m in definition.modules


def test_module_sort() -> None:
    trivial = KModule('trivial', count())
    with trivial as tr:
        assert tr.sorts == (), 'Expect no initial sorts'

        # Add a sort
        ssort = tr.sort('trivial_s')
        assert isinstance(ssort, KSort), f'Expect a sort object, got {str(ssort)}'
        assert ssort in tr.sorts, 'Expect the sort to be in the module'
        assert len(tr.sorts) == 1, 'Expect the only sort in the module'

        # It is forbidden to add sorts twice
        with raises(ValueError):
            tr.sort('trivial_s')

        # It is forbidden to add hooked sorts with the same names as existing sorts
        with raises(ValueError):
            tr.hooked_sort('trivial_s')

        hookeds = tr.hooked_sort('trivial_hooked_s')
        assert hookeds in tr.sorts, 'Expect the hooked sort to be in the module'
        assert set(tr.sorts) == {ssort, hookeds}, 'Expect two sorts in the module'

        # It is forbidden to add sorts with the same names as existing hooked sorts
        with raises(ValueError):
            tr.sort('trivial_hooked_s')


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

        fsymbol = tr.symbol('fbar', ssort, (ssort,), is_functional=True)
        assert fsymbol in tr.symbols, 'Expect the functional symbol to be in the module'
        assert set(tr.symbols) == {ssymbol, fsymbol}, 'Expect two symbols in the module'
        assert fsymbol.is_functional, 'Expect the functional symbol to be functional'

        csymbol = tr.symbol('cbar', ssort, (ssort,), is_ctor=True)
        assert csymbol in tr.symbols, 'Expect the constructor symbol to be in the module'
        assert csymbol.is_ctor, 'Expect the constructor symbol to be a constructor'

        cell_symbol = tr.symbol('cell', ssort, (ssort,), is_cell=True)
        assert cell_symbol in tr.symbols, 'Expect the cell symbol to be in the module'
        assert cell_symbol.is_cell, 'Expect the cell symbol to be a cell'
