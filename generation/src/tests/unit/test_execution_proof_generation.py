from __future__ import annotations

from typing import TYPE_CHECKING

from pytest import fixture

from proof_generation.k.execution_proof_generation import ExecutionProofExp, generate_proofs
from proof_generation.k.kore_convertion.language_semantics import KSortVar, LanguageSemantics
from proof_generation.k.kore_convertion.rewrite_steps import RewriteStepExpression
from proof_generation.pattern import MetaVar
from proof_generation.proofs.kore import kore_kseq, kore_rewrites

if TYPE_CHECKING:
    from proof_generation.pattern import Pattern


@fixture
def double_rewrite() -> tuple[list[RewriteStepExpression], LanguageSemantics]:
    # Constructs a language semantics for the double rewrite module.
    semantics = LanguageSemantics()
    with semantics as sem:
        double_rwrite = sem.module('double-rewrite')
        with double_rwrite as mod:
            sort = mod.sort('some_sort')
            a_symbol = mod.symbol('a', sort, is_functional=True, is_ctor=True)
            b_symbol = mod.symbol('b', sort, is_functional=True, is_ctor=True)
            c_symbol = mod.symbol('c', sort, is_functional=True, is_ctor=True)

            # TODO: Add side conditions!
            rewrite_rule1 = mod.rewrite_rule(
                kore_rewrites(sort.aml_symbol, a_symbol.aml_notation(), b_symbol.aml_notation())
            )
            rewrite_rule2 = mod.rewrite_rule(
                kore_rewrites(sort.aml_symbol, b_symbol.aml_notation(), c_symbol.aml_notation())
            )

    # Construct RewriteStepExpression
    step_one = RewriteStepExpression(
        a_symbol.aml_notation(),
        b_symbol.aml_notation(),
        rewrite_rule1,
        {},
    )
    step_two = RewriteStepExpression(
        b_symbol.aml_notation(),
        c_symbol.aml_notation(),
        rewrite_rule2,
        {},
    )
    hints = [step_one, step_two]

    return hints, semantics


@fixture
def rewrite_with_cell() -> tuple[list[RewriteStepExpression], LanguageSemantics]:
    # TODO: Add side conditions!
    def config_pattern(kitem1: Pattern, kitem2: Pattern) -> Pattern:
        return top_cell_symbol.aml_notation(
            k_cell_symbol.aml_notation(kore_kseq(inj_symbol.aml_notation(kitem1), kitem2))
        )

    semantics = LanguageSemantics()
    with semantics as sem:
        double_rwrite = sem.module('double-rewrite')
        with double_rwrite as mod:
            top_cell_sort = mod.sort('SortGeneratedTopCell')
            k_cell_sort = mod.sort('SortKCell')
            k_sort = mod.sort('SortK')
            foo_sort = mod.sort('SortFoo')

            top_cell_symbol = mod.symbol(
                'generated_top', top_cell_sort, (k_cell_sort,), is_functional=True, is_ctor=True, is_cell=True
            )
            k_cell_symbol = mod.symbol('k', k_cell_sort, (k_sort,), is_functional=True, is_ctor=True, is_cell=True)
            inj_symbol = mod.symbol('inj', KSortVar('To'), (KSortVar('From'),))
            a_symbol = mod.symbol('a', foo_sort, is_functional=True, is_ctor=True)
            b_symbol = mod.symbol('b', foo_sort, is_functional=True, is_ctor=True)
            c_symbol = mod.symbol('c', foo_sort, is_functional=True, is_ctor=True)
            dot_k_symbol = mod.symbol('dotk', k_sort, is_functional=True, is_ctor=True)

            c1 = config_pattern(a_symbol.aml_notation(), MetaVar(0))
            c2 = config_pattern(b_symbol.aml_notation(), MetaVar(0))
            c3 = config_pattern(c_symbol.aml_notation(), MetaVar(0))
            rewrite_rule1 = mod.rewrite_rule(kore_rewrites(top_cell_sort.aml_symbol, c1, c2))
            rewrite_rule2 = mod.rewrite_rule(kore_rewrites(top_cell_sort.aml_symbol, c2, c3))

    # Construct RewriteStepExpression
    step_one = RewriteStepExpression(
        config_pattern(a_symbol.aml_notation(), dot_k_symbol.aml_notation()),
        config_pattern(b_symbol.aml_notation(), dot_k_symbol.aml_notation()),
        rewrite_rule1,
        {0: dot_k_symbol.aml_notation()},
    )
    step_two = RewriteStepExpression(
        config_pattern(b_symbol.aml_notation(), dot_k_symbol.aml_notation()),
        config_pattern(c_symbol.aml_notation(), dot_k_symbol.aml_notation()),
        rewrite_rule2,
        {0: dot_k_symbol.aml_notation()},
    )
    hints = [step_one, step_two]

    return hints, semantics


def test_double_rewrite_semantics(double_rewrite: tuple[list[RewriteStepExpression], LanguageSemantics]) -> None:
    hints, semantics = double_rewrite

    # Test adding axioms
    proof_expr = ExecutionProofExp(list(semantics.notations))
    proof_expr.add_axioms(hints[0], semantics)
    assert proof_expr._axioms == [hints[0].axiom.pattern]
    proof_expr.add_axioms(hints[1], semantics)
    assert proof_expr._axioms == [hints[0].axiom.pattern, hints[1].axiom.pattern]

    # Test proving
    sort = semantics.get_sort('some_sort')
    claim1 = kore_rewrites(sort.aml_symbol, hints[0].configuration_before, hints[0].configuration_after)
    claim2 = kore_rewrites(sort.aml_symbol, hints[1].configuration_before, hints[1].configuration_after)
    proof1 = proof_expr.prove_rewrite_step(claim1, hints[0].axiom.pattern, hints[0].substitutions)
    assert proof1.conc == claim1
    assert proof_expr._claims == [claim1]
    assert proof_expr._proof_expressions == [proof1]
    proof2 = proof_expr.prove_rewrite_step(claim2, hints[1].axiom.pattern, hints[1].substitutions)
    assert proof2.conc == claim2
    assert proof_expr._proof_expressions == [proof1, proof2]
    assert proof_expr._claims == [claim1, claim2]

    # Test generating proofs function
    proof_expr = generate_proofs(iter(hints), semantics)
    assert proof_expr._axioms == [hints[0].axiom.pattern, hints[1].axiom.pattern]
    assert proof_expr._claims == [claim1, claim2]
    assert [p.conc for p in proof_expr._proof_expressions] == [p.conc for p in (proof1, proof2)]

    # Test pretty printing
    opts = proof_expr.pretty_options()
    expected_string1 = '(kore_a() k=> kore_b()):ksort_some_sort'
    expected_string2 = '(kore_b() k=> kore_c()):ksort_some_sort'
    assert hints[0].axiom.pattern.pretty(opts) == expected_string1
    assert hints[1].axiom.pattern.pretty(opts) == expected_string2
    assert claim1.pretty(opts) == expected_string1
    assert claim2.pretty(opts) == expected_string2


def test_rewrite_with_cells(rewrite_with_cell: tuple[list[RewriteStepExpression], LanguageSemantics]) -> None:
    hints, semantics = rewrite_with_cell

    # Test adding axioms
    proof_expr = ExecutionProofExp(list(semantics.notations))
    proof_expr.add_axioms(hints[0], semantics)
    assert proof_expr._axioms == [hints[0].axiom.pattern]
    proof_expr.add_axioms(hints[1], semantics)
    assert proof_expr._axioms == [hints[0].axiom.pattern, hints[1].axiom.pattern]

    # Test proving
    sort = semantics.get_sort('SortGeneratedTopCell')
    claim1 = kore_rewrites(sort.aml_symbol, hints[0].configuration_before, hints[0].configuration_after)
    claim2 = kore_rewrites(sort.aml_symbol, hints[1].configuration_before, hints[1].configuration_after)
    proof1 = proof_expr.prove_rewrite_step(claim1, hints[0].axiom.pattern, hints[0].substitutions)
    assert proof1.conc == claim1
    assert proof_expr._claims == [claim1]
    assert proof_expr._proof_expressions == [proof1]
    proof2 = proof_expr.prove_rewrite_step(claim2, hints[1].axiom.pattern, hints[1].substitutions)
    assert proof2.conc == claim2
    assert proof_expr._proof_expressions == [proof1, proof2]
    assert proof_expr._claims == [claim1, claim2]

    # Test generating proofs function
    proof_expr = generate_proofs(iter(hints), semantics)
    assert proof_expr._axioms == [hints[0].axiom.pattern, hints[1].axiom.pattern]
    assert proof_expr._claims == [claim1, claim2]
    assert [p.conc for p in proof_expr._proof_expressions] == [p.conc for p in (proof1, proof2)]

    # Test pretty printing
    def pretty_conf(symbol_name: str, plug: str = 'phi0') -> str:
        return f'<kore_generated_top> <kore_k> (kore_inj({symbol_name}()) ~> {plug}) </kore_k> </kore_generated_top>'

    opts = proof_expr.pretty_options()
    assert (
        hints[0].axiom.pattern.pretty(opts)
        == '(' + pretty_conf('kore_a') + ' k=> ' + pretty_conf('kore_b') + '):ksort_SortGeneratedTopCell'
    )
    assert (
        hints[1].axiom.pattern.pretty(opts)
        == '(' + pretty_conf('kore_b') + ' k=> ' + pretty_conf('kore_c') + '):ksort_SortGeneratedTopCell'
    )
    assert (
        claim1.pretty(opts)
        == '('
        + pretty_conf('kore_a', 'kore_dotk()')
        + ' k=> '
        + pretty_conf('kore_b', 'kore_dotk()')
        + '):ksort_SortGeneratedTopCell'
    )
    assert (
        claim2.pretty(opts)
        == '('
        + pretty_conf('kore_b', 'kore_dotk()')
        + ' k=> '
        + pretty_conf('kore_c', 'kore_dotk()')
        + '):ksort_SortGeneratedTopCell'
    )
