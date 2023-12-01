from __future__ import annotations

from typing import TYPE_CHECKING

import pytest

from proof_generation.k.execution_proof_generation import ExecutionProofExp, SimplificationInfo, SimplificationVisitor
from proof_generation.k.kore_convertion.language_semantics import KEquationalRule, KRewritingRule
from proof_generation.k.kore_convertion.rewrite_steps import RewriteStepExpression
from proof_generation.pattern import Instantiate
from proof_generation.proofs.kore import kore_rewrites
from tests.unit.test_kore_language_semantics import (
    cell_config_pattern,
    double_rewrite,
    node_tree,
    rewrite_with_cell,
    simplified_cell_config_pattern,
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
    return f'<ksymb_generated_top> <ksymb_k> (ksymb_inj(ksort_SortFoo, ksort_SortKCell, {symbol_name}()) ~> {plug}) </ksymb_k> </ksymb_generated_top>'


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
        ('(ksymb_a() k=> ksymb_b()):ksort_some_sort', '(ksymb_b() k=> ksymb_c()):ksort_some_sort'),
        ('ksymb_a()', 'ksymb_b()', 'ksymb_c()'),
        ('(ksymb_a() k=> ksymb_b()):ksort_some_sort', '(ksymb_b() k=> ksymb_c()):ksort_some_sort'),
    ),
    (
        rewrite_with_cell,
        rewrite_hints_with_cell,
        (
            '(' + cell_pretty_conf('ksymb_a') + ' k=> ' + cell_pretty_conf('ksymb_b') + '):ksort_SortGeneratedTopCell',
            '(' + cell_pretty_conf('ksymb_b') + ' k=> ' + cell_pretty_conf('ksymb_c') + '):ksort_SortGeneratedTopCell',
        ),
        (
            cell_pretty_conf('ksymb_a', 'ksymb_dotk()'),
            cell_pretty_conf('ksymb_b', 'ksymb_dotk()'),
            cell_pretty_conf('ksymb_c', 'ksymb_dotk()'),
        ),
        (
            '('
            + cell_pretty_conf('ksymb_a', 'ksymb_dotk()')
            + ' k=> '
            + cell_pretty_conf('ksymb_b', 'ksymb_dotk()')
            + '):ksort_SortGeneratedTopCell',
            '('
            + cell_pretty_conf('ksymb_b', 'ksymb_dotk()')
            + ' k=> '
            + cell_pretty_conf('ksymb_c', 'ksymb_dotk()')
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


def test_visitor_get_subpattern():
    semantics = node_tree()
    reverse_symbol = semantics.get_symbol('reverse')
    node_symbol = semantics.get_symbol('node')
    a_symbol = semantics.get_symbol('a')
    b_symbol = semantics.get_symbol('b')

    intermidiate_config = simplified_cell_config_pattern(
        semantics,
        'SortTree',
        reverse_symbol.aml_notation(node_symbol.aml_notation(a_symbol.aml_notation(), b_symbol.aml_notation())),
    )

    subpattern1 = reverse_symbol.aml_notation(
        node_symbol.aml_notation(a_symbol.aml_notation(), b_symbol.aml_notation())
    )
    subpattern2 = node_symbol.aml_notation(a_symbol.aml_notation(), b_symbol.aml_notation())
    subpattern3 = a_symbol.aml_notation()
    subpattern4 = b_symbol.aml_notation()

    visitor = SimplificationVisitor(semantics, intermidiate_config)

    assert visitor.get_subpattern((0, 0), intermidiate_config) == subpattern1
    assert visitor.get_subpattern((0,), subpattern1) == subpattern2
    assert visitor.get_subpattern((0, 0), subpattern1) == subpattern3
    assert visitor.get_subpattern((0, 1), subpattern1) == subpattern4


def test_visitor_update_subpattern():
    semantics = node_tree()
    reverse_symbol = semantics.get_symbol('reverse')
    node_symbol = semantics.get_symbol('node')
    a_symbol = semantics.get_symbol('a')
    b_symbol = semantics.get_symbol('b')

    initial_expression = node_symbol.aml_notation(
        reverse_symbol.aml_notation(a_symbol.aml_notation()), reverse_symbol.aml_notation(b_symbol.aml_notation())
    )
    intermidiate_config = simplified_cell_config_pattern(semantics, 'SortTree', initial_expression)

    location = (0, 0, 1)
    plug = b_symbol.aml_notation()
    result = simplified_cell_config_pattern(
        semantics,
        'SortTree',
        node_symbol.aml_notation(reverse_symbol.aml_notation(a_symbol.aml_notation()), b_symbol.aml_notation()),
    )
    assert result == SimplificationVisitor.update_subterm(location, intermidiate_config, plug)

    location = (0,)
    pattern = initial_expression
    plug = b_symbol.aml_notation()
    result = node_symbol.aml_notation(a_symbol.aml_notation(), reverse_symbol.aml_notation(b_symbol.aml_notation()))
    assert result == SimplificationVisitor.update_subterm(location, pattern, plug)


def test_visitor_apply_substitution():
    semantics = node_tree()
    reverse_symbol = semantics.get_symbol('reverse')
    node_symbol = semantics.get_symbol('node')
    a_symbol = semantics.get_symbol('a')
    b_symbol = semantics.get_symbol('b')

    rule = semantics.get_axiom(4)
    assert isinstance(rule, KEquationalRule)
    substitution = {0: a_symbol.aml_notation(), 1: b_symbol.aml_notation()}
    assert SimplificationVisitor.apply_substitutions(rule.right, substitution) == node_symbol.aml_notation(
        reverse_symbol.aml_notation(a_symbol.aml_notation()), reverse_symbol.aml_notation(b_symbol.aml_notation())
    )

    rule = semantics.get_axiom(2)
    assert isinstance(rule, KEquationalRule)
    base_simplifications = rule.substitutions_from_requires
    assert SimplificationVisitor.apply_substitutions(rule.right, base_simplifications) == a_symbol.aml_notation()


def test_visitor_update_config():
    semantics = node_tree()
    reverse_symbol = semantics.get_symbol('reverse')
    node_symbol = semantics.get_symbol('node')
    a_symbol = semantics.get_symbol('a')
    b_symbol = semantics.get_symbol('b')

    intermidiate_config1 = simplified_cell_config_pattern(
        semantics,
        'SortTree',
        node_symbol.aml_notation(
            reverse_symbol.aml_notation(a_symbol.aml_notation()), reverse_symbol.aml_notation(b_symbol.aml_notation())
        ),
    )
    intermidiate_config2 = simplified_cell_config_pattern(
        semantics,
        'SortTree',
        reverse_symbol.aml_notation(node_symbol.aml_notation(a_symbol.aml_notation(), b_symbol.aml_notation())),
    )

    visitor = SimplificationVisitor(semantics, intermidiate_config1)
    assert visitor.simplified_configuration == intermidiate_config1

    # Update the configuration
    visitor.update_configuration(intermidiate_config2)
    assert visitor.simplified_configuration == intermidiate_config2

    # Check that it is not possible to update the configuration during the simplification
    with pytest.raises(AssertionError):
        with visitor:
            visitor.update_configuration(intermidiate_config1)
    with pytest.raises(AssertionError):
        with visitor:
            visitor(0, {}, (0, 0))
            visitor.update_configuration(intermidiate_config1)

    # But it is possible to update the configuration after the simplification
    simple_config = simplified_cell_config_pattern(
        semantics, 'SortTree', reverse_symbol.aml_notation(a_symbol.aml_notation())
    )
    visitor = SimplificationVisitor(semantics, simple_config)
    with visitor:
        visitor(2, {}, (0, 0))  # reverse(a) -> a
        visitor.update_configuration(intermidiate_config1)
    assert visitor.simplified_configuration == simplified_cell_config_pattern(
        semantics, 'SortTree', a_symbol.aml_notation()
    )
    visitor.update_configuration(intermidiate_config1)
    assert visitor.simplified_configuration == intermidiate_config1


def test_subpattern_batch():
    semantics = node_tree()
    reverse_symbol = semantics.get_symbol('reverse')
    node_symbol = semantics.get_symbol('node')
    a_symbol = semantics.get_symbol('a')
    b_symbol = semantics.get_symbol('b')

    # Rules
    # reverse(node(T1, T2)) <-> node(reverse(T2), reverse(T1))
    rec_case = semantics.get_axiom(4)
    assert isinstance(rec_case, KEquationalRule)
    # reverse(b) <-> b
    base_case_b = semantics.get_axiom(3)
    assert isinstance(base_case_b, KEquationalRule)
    # reverse(a) <-> a
    base_case_a = semantics.get_axiom(2)
    assert isinstance(base_case_a, KEquationalRule)

    initial_subterm = reverse_symbol.aml_notation(
        node_symbol.aml_notation(a_symbol.aml_notation()), b_symbol.aml_notation()
    )
    initial_config = simplified_cell_config_pattern(semantics, 'SortTree', initial_subterm)
    proof_obj = ExecutionProofExp(semantics, initial_config)
    proof_obj.simplification_event(rec_case.ordinal, {0: a_symbol.aml_notation(), 1: b_symbol.aml_notation()}, (0, 0))
    expected_stack = [
        SimplificationInfo(
            (0, 0),
            initial_subterm,
            node_symbol.aml_notation(
                reverse_symbol.aml_notation(b_symbol.aml_notation()),
                reverse_symbol.aml_notation(a_symbol.aml_notation()),
            ),
            2,
        )
    ]
    assert proof_obj._simplification_visitor._simplification_stack == expected_stack

    proof_obj.simplification_event(base_case_b.ordinal, {}, (0,))
    expected_stack = [SimplificationInfo((0, 0), initial_subterm, b_symbol.aml_notation(), 1)]
    assert proof_obj._simplification_visitor._simplification_stack == expected_stack

    proof_obj.simplification_event(base_case_a.ordinal, {}, (1,))
    assert proof_obj._simplification_visitor._simplification_stack == []

    # Check the final update of the configuration
    assert proof_obj.current_configuration == simplified_cell_config_pattern(
        semantics, 'SortTree', node_symbol.aml_notation(b_symbol.aml_notation(), a_symbol.aml_notation())
    )
