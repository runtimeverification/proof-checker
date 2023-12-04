from __future__ import annotations

from typing import TYPE_CHECKING

import pytest

from proof_generation.k.execution_proof_generation import ExecutionProofExp
from proof_generation.k.kore_convertion.language_semantics import KRewritingRule
from proof_generation.k.kore_convertion.rewrite_steps import RewriteStepExpression
from proof_generation.pattern import Instantiate, top
from proof_generation.proofs.kore import kore_and, kore_equals, kore_implies, kore_rewrites, kore_top
from tests.unit.test_kore_language_semantics import (
    cell_config_pattern,
    double_rewrite,
    rewrite_with_cell,
    simple_semantics,
)

if TYPE_CHECKING:
    from collections.abc import Callable

    from proof_generation.k.kore_convertion.language_semantics import LanguageSemantics


def rewrite_hints() -> list[RewriteStepExpression]:
    semantics = double_rewrite()
    a_symbol = semantics.get_symbol('a')
    b_symbol = semantics.get_symbol('b')
    c_symbol = semantics.get_symbol('c')
    rewrite_rule1 = semantics.get_axiom(0)
    rewrite_rule2 = semantics.get_axiom(1)

    # Construct RewriteStepExpression
    step_one = RewriteStepExpression(
        a_symbol.app(),
        b_symbol.app(),
        rewrite_rule1,
        {},
    )
    step_two = RewriteStepExpression(
        b_symbol.app(),
        c_symbol.app(),
        rewrite_rule2,
        {},
    )
    return [step_one, step_two]


def rewrite_hints_with_cell() -> list[RewriteStepExpression]:
    semantics = rewrite_with_cell()
    a_symbol = semantics.get_symbol('a')
    b_symbol = semantics.get_symbol('b')
    c_symbol = semantics.get_symbol('c')
    dot_k_symbol = semantics.get_symbol('dotk')
    rewrite_rule1 = semantics.get_axiom(0)
    rewrite_rule2 = semantics.get_axiom(1)

    # Construct RewriteStepExpression
    step_one = RewriteStepExpression(
        cell_config_pattern(semantics, a_symbol.app(), dot_k_symbol.app()),
        cell_config_pattern(semantics, b_symbol.app(), dot_k_symbol.app()),
        rewrite_rule1,
        {0: dot_k_symbol.app()},
    )
    step_two = RewriteStepExpression(
        cell_config_pattern(semantics, b_symbol.app(), dot_k_symbol.app()),
        cell_config_pattern(semantics, c_symbol.app(), dot_k_symbol.app()),
        rewrite_rule2,
        {0: dot_k_symbol.app()},
    )
    return [step_one, step_two]


def cell_pretty_conf(symbol_name: str, plug: str = 'phi0') -> str:
    return f'<ksym_generated_top> <ksym_k> (ksym_inj(ksort_SortFoo, ksort_SortKCell, {symbol_name}()) ~> {plug}) </ksym_k> </ksym_generated_top>'


rewrite_test_parameters = [(double_rewrite, rewrite_hints), (rewrite_with_cell, rewrite_hints_with_cell)]


@pytest.mark.parametrize('rewrite_pat', rewrite_test_parameters)
def test_double_rewrite_semantics(rewrite_pat: tuple[Callable, Callable]) -> None:
    semantics_builder, hints_builder = rewrite_pat
    hints: list[RewriteStepExpression] = hints_builder()
    semantics: LanguageSemantics = semantics_builder()
    assert isinstance(hints[0].axiom.pattern, Instantiate)
    sort_symbol = hints[0].axiom.pattern.inst[0]
    claim1 = kore_rewrites(sort_symbol, hints[0].configuration_before, hints[0].configuration_after)
    claim2 = kore_rewrites(sort_symbol, hints[1].configuration_before, hints[1].configuration_after)

    # Create an instance of the class
    proof_expr = ExecutionProofExp(semantics, init_config=hints[0].configuration_before)
    assert proof_expr.initial_configuration == hints[0].configuration_before
    assert proof_expr.current_configuration == hints[0].configuration_before
    assert isinstance(hints[0].axiom, KRewritingRule)

    # Make the first rewrite step
    assert isinstance(hints[0].axiom, KRewritingRule)
    proof_expr.rewrite_event(hints[0].axiom, hints[0].substitutions)
    assert proof_expr.initial_configuration == hints[0].configuration_before
    assert proof_expr.current_configuration == hints[0].configuration_after
    assert hints[0].axiom.pattern in proof_expr._axioms
    assert proof_expr._claims == [claim1]
    assert len(proof_expr._proof_expressions) == 1
    assert proof_expr._proof_expressions[0].conc == claim1

    # Test the second rewrite step
    assert isinstance(hints[1].axiom, KRewritingRule)
    proof_expr.rewrite_event(hints[1].axiom, hints[1].substitutions)
    assert proof_expr.initial_configuration == hints[0].configuration_before
    assert proof_expr.current_configuration == hints[1].configuration_after
    # TODO: Test other assumptions after the functional substitution is fully implemented
    assert set(proof_expr._axioms).issuperset({hints[0].axiom.pattern, hints[1].axiom.pattern})
    assert proof_expr._claims == [claim1, claim2]
    assert len(proof_expr._proof_expressions) == 2
    assert proof_expr._proof_expressions[1].conc == claim2

    # Test generating proofs function
    generated_proof_expr = ExecutionProofExp.from_proof_hints(iter(hints), semantics)
    assert isinstance(generated_proof_expr, ExecutionProofExp)
    # TODO: Test other assumptions after the functional substitution is fully implemented
    assert set(generated_proof_expr._axioms).issuperset({hints[0].axiom.pattern, hints[1].axiom.pattern})
    assert generated_proof_expr._claims == [claim1, claim2]
    assert [p.conc for p in generated_proof_expr._proof_expressions] == [claim1, claim2]


pretty_print_testing = [
    (
        double_rewrite,
        rewrite_hints,
        ('(ksym_a() k=> ksym_b()):ksort_some_sort', '(ksym_b() k=> ksym_c()):ksort_some_sort'),
        ('ksym_a()', 'ksym_b()', 'ksym_c()'),
        ('(ksym_a() k=> ksym_b()):ksort_some_sort', '(ksym_b() k=> ksym_c()):ksort_some_sort'),
    ),
    (
        rewrite_with_cell,
        rewrite_hints_with_cell,
        (
            '(' + cell_pretty_conf('ksym_a') + ' k=> ' + cell_pretty_conf('ksym_b') + '):ksort_SortGeneratedTopCell',
            '(' + cell_pretty_conf('ksym_b') + ' k=> ' + cell_pretty_conf('ksym_c') + '):ksort_SortGeneratedTopCell',
        ),
        (
            cell_pretty_conf('ksym_a', 'ksym_dotk()'),
            cell_pretty_conf('ksym_b', 'ksym_dotk()'),
            cell_pretty_conf('ksym_c', 'ksym_dotk()'),
        ),
        (
            '('
            + cell_pretty_conf('ksym_a', 'ksym_dotk()')
            + ' k=> '
            + cell_pretty_conf('ksym_b', 'ksym_dotk()')
            + '):ksort_SortGeneratedTopCell',
            '('
            + cell_pretty_conf('ksym_b', 'ksym_dotk()')
            + ' k=> '
            + cell_pretty_conf('ksym_c', 'ksym_dotk()')
            + '):ksort_SortGeneratedTopCell',
        ),
    ),
]


@pytest.mark.parametrize('rewrite_pat', pretty_print_testing)
def test_pretty_printing(  # Detailed type annotations for Callable are given below
    rewrite_pat: tuple[Callable, Callable, tuple[str, ...], tuple[str, ...], tuple[str, ...]]
) -> None:
    semantics_builder, hints_builder, axioms, configurations, claims = rewrite_pat
    semantics: LanguageSemantics = semantics_builder()
    hints: list[RewriteStepExpression] = hints_builder()

    # Create an instance of the class
    proof_expr = ExecutionProofExp(semantics, init_config=hints[0].configuration_before)
    assert proof_expr.initial_configuration.pretty(proof_expr.pretty_options()) == configurations[0]

    # First rewrite step
    assert isinstance(hints[0].axiom, KRewritingRule)
    proved = proof_expr.rewrite_event(hints[0].axiom, hints[0].substitutions)
    assert hints[0].axiom.pattern.pretty(proof_expr.pretty_options()) == axioms[0]
    assert proof_expr.current_configuration.pretty(proof_expr.pretty_options()) == configurations[1]
    assert proved.conc.pretty(proof_expr.pretty_options()) == claims[0]

    # Second rewrite step
    assert isinstance(hints[1].axiom, KRewritingRule)
    proved = proof_expr.rewrite_event(hints[1].axiom, hints[1].substitutions)
    assert hints[1].axiom.pattern.pretty(proof_expr.pretty_options()) == axioms[1]
    assert proof_expr.current_configuration.pretty(proof_expr.pretty_options()) == configurations[2]
    assert proved.conc.pretty(proof_expr.pretty_options()) == claims[1]


def test_simple_rules_pretty_printing() -> None:
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
    rhs_with_ensures1 = kore_and(sort1.aml_symbol, right1, ensures1)
    equation_pattern1 = kore_implies(
        sort1.aml_symbol, requires1, kore_equals(sort1.aml_symbol, sort1.aml_symbol, left1, rhs_with_ensures1)
    )

    requires2 = kore_top(sort1.aml_symbol)
    left2 = sym4.app()
    right2 = sym2.app(sym1.aml_symbol)
    ensures2 = kore_top(sort2.aml_symbol)
    rhs_with_ensures2 = kore_and(sort2.aml_symbol, right2, ensures2)
    equation_pattern2 = kore_implies(
        sort2.aml_symbol,
        requires2,
        kore_equals(sort2.aml_symbol, sort2.aml_symbol, left2, rhs_with_ensures2),
    )

    with mod as m:
        rewrite_rule = m.rewrite_rule(rewrite_pattern)
        equation_rule1 = m.equational_rule(equation_pattern1)
        equation_rule2 = m.equational_rule(equation_pattern2)

    # Check pretty printed versions
    pretty_opt = ExecutionProofExp(semantics, init_config=top()).pretty_options()
    assert rewrite_rule.pattern.pretty(pretty_opt) == '(ksym_sym1 k=> ksym_sym2(ksym_sym1)):ksort_srt1'
    assert (
        equation_rule1.pattern.pretty(pretty_opt)
        == '(k⊤:ksort_srt1 k-> (ksym_sym1():ksort_srt1 k= (ksym_sym3() k⋀ k⊤:ksort_srt1):ksort_srt1):ksort_srt1):ksort_srt1'
    )
    assert (
        equation_rule2.pattern.pretty(pretty_opt)
        == '(k⊤:ksort_srt2 k-> (ksym_sym4():ksort_srt2 k= (ksym_sym2(ksym_sym1) k⋀ k⊤:ksort_srt2):ksort_srt2):ksort_srt2):ksort_srt2'
    )
