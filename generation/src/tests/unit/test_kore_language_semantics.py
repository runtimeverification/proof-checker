from __future__ import annotations

from itertools import count

from pytest import mark, raises

from proof_generation.aml import App, EVar, Pattern, Symbol, phi0, phi1
from proof_generation.k.execution_proof_generation import ExecutionProofExp
from proof_generation.k.kore_convertion.language_semantics import (
    KEquationalRule,
    KModule,
    KSort,
    KSortVar,
    KSymbol,
    LanguageSemantics,
)
from proof_generation.proofs.definedness import equals, floor, functional, subset
from proof_generation.proofs.kore import (
    KoreLemmas,
    ceil,
    kore_and,
    kore_equals,
    kore_implies,
    kore_in,
    kore_kseq,
    kore_rewrites,
    kore_top,
    nary_app,
)


def double_rewrite() -> LanguageSemantics:
    # Constructs a language semantics for the double rewrite module.
    semantics = LanguageSemantics()
    with semantics as sem:
        double_rewrite = sem.module('double-rewrite')
        with double_rewrite as mod:
            sort = mod.sort('some_sort')
            a_symbol = mod.symbol('a', sort, is_functional=True, is_ctor=True)
            b_symbol = mod.symbol('b', sort, is_functional=True, is_ctor=True)
            c_symbol = mod.symbol('c', sort, is_functional=True, is_ctor=True)

            # TODO: Add side conditions!
            mod.rewrite_rule(kore_rewrites(sort.aml_symbol, a_symbol.app(), b_symbol.app()))
            mod.rewrite_rule(kore_rewrites(sort.aml_symbol, b_symbol.app(), c_symbol.app()))
    return semantics


def rewrite_with_cell() -> LanguageSemantics:
    semantics = LanguageSemantics()
    with semantics as sem:
        double_rewrite = sem.module('double-rewrite')
        with double_rewrite as mod:
            top_cell_sort = mod.sort('SortGeneratedTopCell')
            k_cell_sort = mod.sort('SortKCell')
            k_sort = mod.sort('SortK')
            foo_sort = mod.sort('SortFoo')

            mod.symbol(
                'generated_top',
                top_cell_sort,
                input_sorts=(k_cell_sort,),
                is_functional=True,
                is_ctor=True,
                is_cell=True,
            )
            mod.symbol('k', k_cell_sort, input_sorts=(k_sort,), is_functional=True, is_ctor=True, is_cell=True)
            from_sort, to_sort = KSortVar('From'), KSortVar('To')
            mod.symbol('inj', to_sort, sort_params=(from_sort, to_sort), input_sorts=(from_sort,))
            a_symbol = mod.symbol('a', foo_sort, is_functional=True, is_ctor=True)
            b_symbol = mod.symbol('b', foo_sort, is_functional=True, is_ctor=True)
            c_symbol = mod.symbol('c', foo_sort, is_functional=True, is_ctor=True)
            mod.symbol('dotk', k_sort, is_functional=True, is_ctor=True)

            c1 = rewrite_with_cells_config_pattern(semantics, a_symbol.app(), EVar(0))
            c2 = rewrite_with_cells_config_pattern(semantics, b_symbol.app(), EVar(0))
            c3 = rewrite_with_cells_config_pattern(semantics, c_symbol.app(), EVar(0))
            mod.rewrite_rule(kore_rewrites(top_cell_sort.aml_symbol, c1, c2))
            mod.rewrite_rule(kore_rewrites(top_cell_sort.aml_symbol, c2, c3))

    return semantics


def node_tree() -> LanguageSemantics:
    semantics = LanguageSemantics()
    with semantics as sem:
        module = sem.module('node-tree')
        with module as mod:
            top_cell_sort_obj = mod.sort('SortGeneratedTopCell')

            kcell_sort_obj = mod.sort('SortKCell')
            k_sort_obj = mod.sort('SortK')

            tree_sort_obj = mod.sort('SortTree')
            tree_sort = tree_sort_obj.aml_symbol
            tree_top = kore_top(tree_sort)

            mod.symbol(
                'generated_top',
                top_cell_sort_obj,
                input_sorts=(kcell_sort_obj,),
                is_functional=True,
                is_ctor=True,
                is_cell=True,
            )
            mod.symbol('k', kcell_sort_obj, input_sorts=(k_sort_obj,), is_functional=True, is_ctor=True, is_cell=True)
            from_sort, to_sort = KSortVar('From'), KSortVar('To')
            mod.symbol('inj', to_sort, sort_params=(from_sort, to_sort), input_sorts=(from_sort,))

            init_symbol = mod.symbol('init', tree_sort_obj, is_functional=True, is_ctor=True)
            next_symbol = mod.symbol('next', tree_sort_obj, is_functional=True, is_ctor=True)
            node_symbol = mod.symbol(
                'node', tree_sort_obj, input_sorts=(tree_sort_obj, tree_sort_obj), is_functional=True, is_ctor=True
            )
            reverse_symbol = mod.symbol('reverse', tree_sort_obj, input_sorts=(tree_sort_obj,), is_functional=True)
            a_symbol = mod.symbol('a', tree_sort_obj, is_functional=True, is_ctor=True)
            b_symbol = mod.symbol('b', tree_sort_obj, is_functional=True, is_ctor=True)

            cfg_sort = semantics.configuration_sort.aml_symbol
            cfg_sort_top = kore_top(cfg_sort)

            # init{}() => next{}()
            init_conf = tree_semantics_config_pattern(semantics, 'SortTree', init_symbol.app())
            next_conf = tree_semantics_config_pattern(semantics, 'SortTree', next_symbol.app())
            mod.rewrite_rule(kore_rewrites(cfg_sort, init_conf, next_conf))

            # next => reverse(node(a, b))
            reverse_expression = reverse_symbol.app(node_symbol.app(a_symbol.app(), b_symbol.app()))
            reverse_conf = tree_semantics_config_pattern(semantics, 'SortTree', reverse_expression)
            mod.rewrite_rule(kore_rewrites(cfg_sort, next_conf, reverse_conf))

            # reverse(a) = a
            requires = kore_and(
                cfg_sort_top,
                kore_and(
                    kore_in(tree_sort, cfg_sort, EVar(0), kore_and(a_symbol.app(), EVar(1))),
                    cfg_sort_top,
                ),
            )
            left = reverse_symbol.app(EVar(0))
            right = EVar(1)
            ensures = tree_top
            equational_pattern = kore_implies(
                cfg_sort,
                requires,
                kore_equals(tree_sort, cfg_sort, left, kore_and(right, ensures)),
            )
            mod.equational_rule(equational_pattern)

            # reverse(b) = b
            requires = kore_and(
                cfg_sort_top,
                kore_and(
                    kore_in(tree_sort, cfg_sort, EVar(0), kore_and(b_symbol.app(), EVar(1))),
                    cfg_sort_top,
                ),
            )
            equational_pattern = kore_implies(
                cfg_sort,
                requires,
                kore_equals(tree_sort, cfg_sort, left, kore_and(right, ensures)),
            )
            mod.equational_rule(equational_pattern)

            # reverse(node(T1, T2)) = node(reverse(T2), reverse(T1))
            requires = kore_and(
                cfg_sort_top,
                kore_and(
                    kore_in(tree_sort, cfg_sort, EVar(0), node_symbol.app(EVar(1), EVar(2))),
                    cfg_sort_top,
                ),
            )
            eq3_left = reverse_symbol.app(EVar(0))
            eq3_right = node_symbol.app(reverse_symbol.app(EVar(2)), reverse_symbol.app(EVar(1)))
            mod.equational_rule(
                kore_implies(
                    cfg_sort,
                    requires,
                    kore_equals(tree_sort, cfg_sort, eq3_left, kore_and(eq3_right, ensures)),
                )
            )

    return semantics


# TODO: Add side conditions!
def rewrite_with_cells_config_pattern(semantics: LanguageSemantics, kitem1: Pattern, kitem2: Pattern) -> Pattern:
    top_cell_symbol = semantics.get_symbol('generated_top')
    k_cell_sort = semantics.get_sort('SortKCell')
    foo_sort = semantics.get_sort('SortFoo')
    k_cell_symbol = semantics.get_symbol('k')
    inj_symbol = semantics.get_symbol('inj')
    return top_cell_symbol.app(
        k_cell_symbol.app(kore_kseq(inj_symbol.app(foo_sort.aml_symbol, k_cell_sort.aml_symbol, kitem1), kitem2))
    )


def tree_semantics_config_pattern(semantics: LanguageSemantics, input_sort_name: str, kitem: Pattern) -> Pattern:
    top_cell_symbol = semantics.get_symbol('generated_top')
    k_cell_sort = semantics.get_sort('SortKCell')
    internal_sort = semantics.get_sort(input_sort_name)
    k_cell_symbol = semantics.get_symbol('k')
    inj_symbol = semantics.get_symbol('inj')
    return top_cell_symbol.app(
        k_cell_symbol.app(inj_symbol.app(internal_sort.aml_symbol, k_cell_sort.aml_symbol, kitem))
    )


def simple_semantics() -> LanguageSemantics:
    semantics = LanguageSemantics()
    with semantics as sem:
        mod = sem.module('test_module')
        with mod as mod:
            srt1 = mod.sort('srt1')
            srt2 = mod.sort('srt2')

            mod.symbol('sym1', srt1)
            mod.symbol('sym2', srt2, input_sorts=(srt1,), is_functional=True)
            mod.symbol('sym3', srt1)
            mod.symbol('sym4', srt2)
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


def test_language_semantics_notations() -> None:
    semantics: LanguageSemantics = simple_semantics()
    expected_notations = {
        *{s.app for s in semantics.main_module.symbols},
    }

    assert isinstance(semantics.notations, tuple)
    assert set(semantics.notations) == expected_notations


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
    # Test the basic case
    srt1 = KSort('srt1')
    sym = KSymbol('sym', (), srt1)
    assert sym.name == 'sym'
    assert sym.output_sort == srt1
    assert sym.aml_symbol == Symbol('ksym_sym')
    assert not sym.is_functional
    assert not sym.is_ctor
    assert not sym.is_cell
    # This is an intentionally strict comparison that also checks that
    # nary_app caching working and it does work even with different
    # equivalent instances of the Symbol class
    # The rest comparisons will be just equality checks
    assert sym.app is nary_app(Symbol(sym.aml_symbol.name), 0, False)

    # Test the creation of a functional symbol
    srt2 = KSort('srt2')
    fsym = KSymbol('fsym', (), srt1, (srt1, srt2), is_functional=True)
    assert fsym.name == 'fsym'
    assert fsym.output_sort == srt1
    assert fsym.input_sorts == (srt1, srt2)
    assert fsym.aml_symbol == Symbol('ksym_fsym')
    assert fsym.is_functional
    assert not fsym.is_ctor
    assert not fsym.is_cell
    assert fsym.app == nary_app(fsym.aml_symbol, 2, False)

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
    assert cell_sym.aml_symbol == Symbol('ksym_cell')
    assert cell_sym.is_functional
    assert not cell_sym.is_ctor
    assert cell_sym.is_cell
    assert cell_sym.app == nary_app(cell_sym.aml_symbol, 2, True)


def test_symbol_params() -> None:
    sort1 = KSort('sort1')
    sort2 = KSortVar('var1')
    sort3 = KSortVar('var2')

    symbol1 = KSymbol('symbol1', (), sort1)
    assert symbol1.input_sorts == ()
    assert symbol1.sort_params == ()
    assert symbol1.aml_symbol == Symbol('ksym_symbol1')
    assert symbol1.app == nary_app(Symbol('ksym_symbol1'), 0, False)

    symbol2 = KSymbol('symbol2', (sort2,), sort1, (sort1, sort2))
    assert symbol2.input_sorts == (sort1, sort2)
    assert symbol2.sort_params == (sort2,)
    assert symbol2.aml_symbol == Symbol('ksym_symbol2')
    assert symbol2.app == nary_app(Symbol('ksym_symbol2'), 3, False)

    symbol3 = KSymbol('symbol3', (sort2, sort3), sort3, (sort1, sort2), is_functional=True)
    assert symbol3.input_sorts == (sort1, sort2)
    assert symbol3.sort_params == (sort2, sort3)
    assert symbol3.aml_symbol == Symbol('ksym_symbol3')
    assert symbol3.app == nary_app(Symbol('ksym_symbol3'), 4, False)

    symbol3 = KSymbol('symbol3', (sort2, sort3), sort3, (sort1, sort2, sort2), is_functional=True, is_cell=True)
    assert symbol3.input_sorts == (sort1, sort2, sort2)
    assert symbol3.sort_params == (sort2, sort3)
    assert symbol3.aml_symbol == Symbol('ksym_symbol3')
    assert symbol3.app == nary_app(Symbol('ksym_symbol3'), 5, True)


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
        with raises(ValueError):
            trivial.get_sort('unknown_sort')
        with raises(ValueError):
            trivial.get_symbol('unknown_symbol')


def test_rules() -> None:
    semantics = simple_semantics()
    sort1 = semantics.get_sort('srt1')
    sort2 = semantics.get_sort('srt2')
    sym1 = semantics.get_symbol('sym1')  # Sort1
    sym2 = semantics.get_symbol('sym2')  # Sort1 -> Sort2
    sym3 = semantics.get_symbol('sym3')  # Sort1
    sym4 = semantics.get_symbol('sym4')  # Sort2
    mod = semantics.main_module

    # Rewrite pattern
    rewrite_pattern = kore_rewrites(sort1.aml_symbol, sym1.aml_symbol, sym2.app(sym1.aml_symbol))

    # Equation patterns
    requires1 = kore_top(sort1.aml_symbol)
    left1 = sym1.app()
    right1 = sym3.app()
    ensures1 = kore_top(sort1.aml_symbol)
    rhs_with_ensures1 = kore_and(right1, ensures1)
    equation_pattern1 = kore_implies(
        sort1.aml_symbol, requires1, kore_equals(sort1.aml_symbol, sort1.aml_symbol, left1, rhs_with_ensures1)
    )

    requires2 = kore_top(sort1.aml_symbol)
    left2 = sym4.app()
    right2 = sym2.app(sym1.aml_symbol)
    ensures2 = kore_top(sort2.aml_symbol)
    rhs_with_ensures2 = kore_and(right2, ensures2)
    equation_pattern2 = kore_implies(
        sort2.aml_symbol,
        requires2,
        kore_equals(sort2.aml_symbol, sort2.aml_symbol, left2, rhs_with_ensures2),
    )

    with mod as m:
        rewrite_rule = m.rewrite_rule(rewrite_pattern)
        equation_rule1 = m.equational_rule(equation_pattern1)
        equation_rule2 = m.equational_rule(equation_pattern2)

    # Check ordinals
    assert rewrite_rule.ordinal == 0
    assert equation_rule1.ordinal == 1
    assert equation_rule2.ordinal == 2

    # Check decomposition of pattern 1
    assert rewrite_rule.pattern == rewrite_pattern
    assert equation_rule1.requires == requires1
    assert equation_rule1.left == left1
    assert equation_rule1.right == right1
    assert equation_rule1.ensures == ensures1
    assert equation_rule1.rhs_with_ensures == rhs_with_ensures1

    # Check the decomposition of pattern 2
    assert equation_rule2.requires == requires2
    assert equation_rule2.left == left2
    assert equation_rule2.right == right2
    assert equation_rule2.ensures == ensures2
    assert equation_rule2.rhs_with_ensures == rhs_with_ensures2

    # Check that the rule is imported
    assert rewrite_rule.pattern == rewrite_pattern
    assert semantics.get_axiom(rewrite_rule.ordinal) == rewrite_rule
    assert mod.get_axiom(rewrite_rule.ordinal) == rewrite_rule

    # Equational rule
    assert equation_rule1.pattern == equation_pattern1
    assert semantics.get_axiom(equation_rule1.ordinal) == equation_rule1
    assert mod.get_axiom(equation_rule1.ordinal) == equation_rule1

    # Another equational rule
    assert equation_rule2.pattern == equation_pattern2
    assert semantics.get_axiom(equation_rule2.ordinal) == equation_rule2
    assert mod.get_axiom(equation_rule2.ordinal) == equation_rule2


def test_module_import() -> None:
    semantics = simple_semantics()
    ever_created_sorts = set(semantics.main_module.sorts)
    ever_created_symbols = set(semantics.main_module.symbols)
    initial_sorts = set(semantics.main_module.sorts)
    initial_symbols = set(semantics.main_module.symbols)

    # Testing expected initial semantics setup
    assert len(semantics.modules) == 1, 'Expect one module'
    assert semantics.main_module.name == 'test_module'
    old_module = semantics.main_module

    # Adding a new module and importing it to the existing one
    added_symbol = None
    added_sort = None
    with semantics as sem:
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
    assert set(semantics.modules) == {new_module, old_module}
    assert semantics.main_module == new_module
    assert semantics.get_module('new_module') == new_module

    # Check that the content of the new module is available in the semantics
    assert added_symbol == semantics.get_symbol('new_module_sym') is not None
    assert added_sort == semantics.get_sort('new_module_srt') is not None
    assert added_symbol == semantics.get_symbol('new_module_sym') is not None
    assert added_sort == semantics.get_sort('new_module_srt') is not None

    # Check that all symbols and sorts are collected recursievly
    assert set(semantics.sorts) == ever_created_sorts
    assert set(semantics.symbols) == ever_created_symbols
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

        pattern_rewrite = kore_rewrites(newest_sort.aml_symbol, newest_symbol.aml_symbol, newest_symbol.aml_symbol)
        pattern_equals = kore_implies(
            newest_sort.aml_symbol,
            kore_top(newest_sort.aml_symbol),
            kore_equals(
                newest_sort.aml_symbol, newest_sort.aml_symbol, newest_symbol.aml_symbol, newest_symbol.aml_symbol
            ),
        )

        assert isinstance(pattern_rewrite, Pattern)
        rewrite_rule = nm.rewrite_rule(pattern_rewrite)
        equation_rule = nm.equational_rule(pattern_equals)
    with semantics.main_module as mm:
        mm.import_module(newest_module)

    # Test that the new module is available in the semantics
    assert newest_module in semantics.modules
    assert set(semantics.modules) == {old_module, new_module, newest_module}
    assert semantics.get_module('newest_module') == newest_module

    # Test that the content is gettable
    assert semantics.get_symbol('newest_module_sym') is newest_symbol
    assert semantics.get_sort('newest_module_srt') is newest_sort
    assert semantics.main_module.get_symbol('newest_module_sym') is newest_symbol
    assert semantics.main_module.get_sort('newest_module_srt') is newest_sort

    # Test accessing added rule
    assert newest_module.get_axiom(rewrite_rule.ordinal) == rewrite_rule
    assert newest_module.get_axiom(equation_rule.ordinal) == equation_rule
    assert semantics.main_module.get_axiom(rewrite_rule.ordinal) == rewrite_rule
    assert semantics.main_module.get_axiom(equation_rule.ordinal) == equation_rule
    assert semantics.get_axiom(rewrite_rule.ordinal) == rewrite_rule
    assert semantics.get_axiom(equation_rule.ordinal) == equation_rule
    with raises(ValueError):
        semantics.get_axiom(rewrite_rule.ordinal + 10)

    # Test final sets of sorts, symbols and notations
    assert set(semantics.sorts) == ever_created_sorts
    assert set(semantics.symbols) == ever_created_symbols
    assert set(old_module.sorts) == initial_sorts
    assert set(old_module.symbols) == initial_symbols
    assert set(new_module.sorts) == {added_sort, newest_sort}
    assert set(new_module.symbols) == {added_symbol, newest_symbol}
    assert set(newest_module.sorts) == {newest_sort}
    assert set(newest_module.symbols) == {newest_symbol}

    # Test that semantics notations are updated
    assert set(semantics.notations) == {
        *{s.app for s in ever_created_symbols},
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
            a = a_symbol.app
            b = b_symbol.aml_symbol
            c = c_symbol.app
            d = d_symbol.app
            single_evar_krule = mod.rewrite_rule(kore_rewrites(sort.aml_symbol, EVar(0), EVar(0)))
            double_evar_krule = mod.rewrite_rule(
                kore_rewrites(sort.aml_symbol, d(EVar(0), EVar(1)), d(EVar(0), EVar(1)))
            )

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
                {0: c(b), 1: b},
            )
            assert functional(c(b)) in cbb_pe.get_axioms()
            assert functional(b) in cbb_pe.get_axioms()


@mark.parametrize(
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


def test_collect_substitution() -> None:
    semantics = node_tree()

    node_symbol = semantics.get_symbol('node')
    a_symbol = semantics.get_symbol('a')
    b_symbol = semantics.get_symbol('b')
    base_equation_a = semantics.get_axiom(2)
    base_equation_b = semantics.get_axiom(3)
    reversed_equation = semantics.get_axiom(4)

    assert isinstance(base_equation_a, KEquationalRule)
    assert base_equation_a.substitutions_from_requires == {0: a_symbol.app(), 1: a_symbol.app()}

    assert isinstance(base_equation_b, KEquationalRule)
    assert base_equation_b.substitutions_from_requires == {0: b_symbol.app(), 1: b_symbol.app()}

    assert isinstance(reversed_equation, KEquationalRule)
    assert reversed_equation.substitutions_from_requires == {0: node_symbol.app(EVar(1), EVar(2))}


def test_locate_simplifications() -> None:
    semantics = node_tree()

    init_rewrite = semantics.get_axiom(0)
    next_rewrite = semantics.get_axiom(1)
    base_equation_a = semantics.get_axiom(2)
    base_equation_b = semantics.get_axiom(3)
    reversed_equation = semantics.get_axiom(4)

    reverse_symbol = semantics.get_symbol('reverse')
    node_symbol = semantics.get_symbol('node')
    a_symbol = semantics.get_symbol('a')
    b_symbol = semantics.get_symbol('b')
    intermediate_config1 = tree_semantics_config_pattern(
        semantics,
        'SortTree',
        node_symbol.app(reverse_symbol.app(a_symbol.app()), reverse_symbol.app(b_symbol.app())),
    )
    intermediate_config2 = tree_semantics_config_pattern(
        semantics,
        'SortTree',
        reverse_symbol.app(node_symbol.app(a_symbol.app(), b_symbol.app())),
    )
    unknown_symbol_conf = tree_semantics_config_pattern(
        semantics, 'SortTree', App(Symbol('unknown_symbol_1'), Symbol('unknown_symbol_2'))
    )

    # Covers the case with cells and functional constructors and cells
    assert semantics.count_simplifications(init_rewrite.pattern) == 0
    # Same plus krewrite and a single use of a functional symbol
    assert semantics.count_simplifications(next_rewrite.pattern) == 1
    # Equational rule with a single use of a functional symbol, no cells
    # but the equation itself contains the function call twice which should be ignored
    assert semantics.count_simplifications(base_equation_a.pattern) == 1
    assert semantics.count_simplifications(base_equation_b.pattern) == 1
    # Three uses of functional symbols
    assert semantics.count_simplifications(reversed_equation.pattern) == 3
    # Explicit configurations with cells
    assert semantics.count_simplifications(intermediate_config1) == 2
    assert semantics.count_simplifications(intermediate_config2) == 1
    # Explicit configuration with an unknown symbol
    assert semantics.count_simplifications(unknown_symbol_conf) == 0
