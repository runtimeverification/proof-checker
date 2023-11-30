from __future__ import annotations

from typing import TYPE_CHECKING

import pytest

from proof_generation.k.execution_proof_generation import ExecutionProofExp
from proof_generation.k.kore_convertion.language_semantics import KRewritingRule
from proof_generation.k.kore_convertion.rewrite_steps import RewriteStepExpression
from proof_generation.pattern import Instantiate
from proof_generation.proofs.kore import kore_rewrites
from tests.unit.test_kore_language_semantics import cell_config_pattern, double_rewrite, rewrite_with_cell

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
        cell_config_pattern(semantics, a_symbol.aml_notation(), dot_k_symbol.aml_notation()),
        cell_config_pattern(semantics, b_symbol.aml_notation(), dot_k_symbol.aml_notation()),
        rewrite_rule1,
        {0: dot_k_symbol.aml_notation()},
    )
    step_two = RewriteStepExpression(
        cell_config_pattern(semantics, b_symbol.aml_notation(), dot_k_symbol.aml_notation()),
        cell_config_pattern(semantics, c_symbol.aml_notation(), dot_k_symbol.aml_notation()),
        rewrite_rule2,
        {0: dot_k_symbol.aml_notation()},
    )
    return [step_one, step_two]


def cell_pretty_conf(symbol_name: str, plug: str = 'phi0') -> str:
    return f'<kore_generated_top> <kore_k> (kore_inj(ksort_SortFoo, ksort_SortKCell, {symbol_name}()) ~> {plug}) </kore_k> </kore_generated_top>'


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
        ('(kore_a() k=> kore_b()):ksort_some_sort', '(kore_b() k=> kore_c()):ksort_some_sort'),
        ('kore_a()', 'kore_b()', 'kore_c()'),
        ('(kore_a() k=> kore_b()):ksort_some_sort', '(kore_b() k=> kore_c()):ksort_some_sort'),
    ),
    (
        rewrite_with_cell,
        rewrite_hints_with_cell,
        (
            '(' + cell_pretty_conf('kore_a') + ' k=> ' + cell_pretty_conf('kore_b') + '):ksort_SortGeneratedTopCell',
            '(' + cell_pretty_conf('kore_b') + ' k=> ' + cell_pretty_conf('kore_c') + '):ksort_SortGeneratedTopCell',
        ),
        (
            cell_pretty_conf('kore_a', 'kore_dotk()'),
            cell_pretty_conf('kore_b', 'kore_dotk()'),
            cell_pretty_conf('kore_c', 'kore_dotk()'),
        ),
        (
            '('
            + cell_pretty_conf('kore_a', 'kore_dotk()')
            + ' k=> '
            + cell_pretty_conf('kore_b', 'kore_dotk()')
            + '):ksort_SortGeneratedTopCell',
            '('
            + cell_pretty_conf('kore_b', 'kore_dotk()')
            + ' k=> '
            + cell_pretty_conf('kore_c', 'kore_dotk()')
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
