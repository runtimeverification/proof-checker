from __future__ import annotations

from typing import TYPE_CHECKING

import pytest

from proof_generation.aml import EVar, Instantiate, top
from proof_generation.interpreter.basic_interpreter import BasicInterpreter, ExecutionPhase
from proof_generation.k.execution_proof_generation import (
    ExecutionProofExp,
    SimplificationInfo,
    SimplificationPerformer,
    SimplificationProver,
)
from proof_generation.k.kore_convertion.language_semantics import KEquationalRule, KRewritingRule
from proof_generation.k.kore_convertion.rewrite_steps import RewriteStepExpression
from proof_generation.proof import ProofThunk
from proof_generation.proofs.kore import kore_and, kore_equals, kore_implies, kore_rewrites, kore_top
from proof_generation.proofs.substitution import HOLE
from tests.unit.test_kore_language_semantics import (
    double_rewrite,
    node_tree,
    rewrite_with_cell,
    rewrite_with_cells_config_pattern,
    simple_semantics,
    tree_semantics_config_pattern,
)
from tests.unit.test_propositional import make_pt

if TYPE_CHECKING:
    from collections.abc import Callable

    from proof_generation.aml import Pattern
    from proof_generation.k.kore_convertion.language_semantics import LanguageSemantics


class DummyProver(SimplificationProver):
    def apply_framing_lemma(self, equality_proof: ProofThunk, context: Pattern) -> ProofThunk:
        sort0, sort1, left, right = kore_equals.assert_matches(equality_proof.conc)
        return make_pt(
            kore_equals(sort0, sort1, context.apply_esubst(HOLE.name, left), context.apply_esubst(HOLE.name, right))
        )

    def equality_proof(
        self, rule: Pattern, base_substitutions: dict[int, Pattern], substitutions: dict[int, Pattern]
    ) -> ProofThunk:
        rule_with_substitution = rule.apply_esubsts(base_substitutions)
        rule_proof_thunk = make_pt(rule_with_substitution)
        # TODO: Remove this prove_equality,
        # This should "know" the result by comparing the "rule" in a simple if statement
        equation_proof = self.prove_equality_from_rule(rule_proof_thunk)
        return make_pt(equation_proof.conc.apply_esubsts(substitutions))

    def equality_transitivity(self, last_proof: ProofThunk, new_proof: ProofThunk) -> ProofThunk:
        sort1, sort2, phi0, phi1 = kore_equals.assert_matches(last_proof.conc)
        sort1_p, sort2_p, phi1_p, phi2 = kore_equals.assert_matches(new_proof.conc)
        assert sort1 == sort1_p
        assert sort2 == sort2_p
        assert phi1 == phi1_p
        return make_pt(kore_equals(sort1, sort2, phi0, phi2))


def rewrite_hints() -> list[tuple[RewriteStepExpression, Pattern, Pattern]]:
    semantics = double_rewrite()
    a_symbol = semantics.get_symbol('a')
    b_symbol = semantics.get_symbol('b')
    c_symbol = semantics.get_symbol('c')
    rewrite_rule1 = semantics.get_axiom(0)
    rewrite_rule2 = semantics.get_axiom(1)

    # Construct RewriteStepExpression
    step_one = RewriteStepExpression(
        rewrite_rule1,
        {},
    )
    step_two = RewriteStepExpression(
        rewrite_rule2,
        {},
    )
    return [(step_one, a_symbol.app(), b_symbol.app()), (step_two, b_symbol.app(), c_symbol.app())]


def rewrite_hints_with_cell() -> list[tuple[RewriteStepExpression, Pattern, Pattern]]:
    semantics = rewrite_with_cell()
    a_symbol = semantics.get_symbol('a')
    b_symbol = semantics.get_symbol('b')
    c_symbol = semantics.get_symbol('c')
    dot_k_symbol = semantics.get_symbol('dotk')
    rewrite_rule1 = semantics.get_axiom(0)
    rewrite_rule2 = semantics.get_axiom(1)

    # Construct RewriteStepExpression
    step_one = RewriteStepExpression(
        rewrite_rule1,
        {0: dot_k_symbol.app()},
    )
    step_two = RewriteStepExpression(
        rewrite_rule2,
        {0: dot_k_symbol.app()},
    )
    return [
        (
            step_one,
            rewrite_with_cells_config_pattern(semantics, a_symbol.app(), dot_k_symbol.app()),
            rewrite_with_cells_config_pattern(semantics, b_symbol.app(), dot_k_symbol.app()),
        ),
        (
            step_two,
            rewrite_with_cells_config_pattern(semantics, b_symbol.app(), dot_k_symbol.app()),
            rewrite_with_cells_config_pattern(semantics, c_symbol.app(), dot_k_symbol.app()),
        ),
    ]


def cell_pretty_conf(symbol_name: str, plug: str = 'phi0') -> str:
    return f'<ksym_generated_top> <ksym_k> (ksym_inj(ksort_SortFoo, ksort_SortKCell, {symbol_name}()) ~> {plug}) </ksym_k> </ksym_generated_top>'


@pytest.mark.parametrize(
    'semantics_builder, hints_builder',
    [
        [double_rewrite, rewrite_hints],
        [rewrite_with_cell, rewrite_hints_with_cell],
    ],
)
def test_double_rewrite_semantics(semantics_builder: Callable, hints_builder: Callable) -> None:
    hints: list[tuple[RewriteStepExpression, Pattern, Pattern]] = hints_builder()
    semantics: LanguageSemantics = semantics_builder()

    hint1, conf_before1, conf_after1 = hints[0]
    hint2, conf_before2, conf_after2 = hints[1]
    assert conf_after1 == conf_before2

    assert isinstance(hint1.axiom.pattern, Instantiate)
    sort_symbol = hint1.axiom.pattern.inst[0]
    claim1 = kore_rewrites(sort_symbol, conf_before1, conf_after1)
    claim2 = kore_rewrites(sort_symbol, conf_before2, conf_after2)

    # Create an instance of the class
    proof_expr = ExecutionProofExp(semantics, init_config=conf_before1)
    assert proof_expr.initial_configuration == conf_before1
    assert proof_expr.current_configuration == conf_before1
    assert isinstance(hint1.axiom, KRewritingRule)

    # Make the first rewrite step
    assert isinstance(hint1.axiom, KRewritingRule)
    proof_expr.rewrite_event(hint1.axiom, hint1.substitutions)
    assert proof_expr.initial_configuration == conf_before1
    assert proof_expr.current_configuration == conf_after1
    assert hint1.axiom.pattern in proof_expr._axioms
    assert proof_expr._claims == [claim1]
    assert len(proof_expr._proof_expressions) == 1
    assert proof_expr._proof_expressions[0].conc == claim1

    # Test the second rewrite step
    assert isinstance(hint2.axiom, KRewritingRule)
    proof_expr.rewrite_event(hint2.axiom, hint2.substitutions)
    assert proof_expr.initial_configuration == conf_before1
    assert proof_expr.current_configuration == conf_after2
    # TODO: Test other assumptions after the functional substitution is fully implemented
    assert set(proof_expr._axioms).issuperset({hint2.axiom.pattern, hint2.axiom.pattern})
    assert proof_expr._claims == [claim1, claim2]
    assert len(proof_expr._proof_expressions) == 2
    assert proof_expr._proof_expressions[1].conc == claim2

    # Test generating proofs function
    generated_proof_expr = ExecutionProofExp.from_proof_hints(conf_before1, iter((hint1, hint2)), semantics)
    assert isinstance(generated_proof_expr, ExecutionProofExp)
    # TODO: Test other assumptions after the functional substitution is fully implemented
    assert set(generated_proof_expr._axioms).issuperset({hint1.axiom.pattern, hint2.axiom.pattern})
    assert generated_proof_expr._claims == [claim1, claim2]
    assert [p.conc for p in generated_proof_expr._proof_expressions] == [claim1, claim2]


def test_rewrite_with_simplification() -> None:
    semantics = node_tree()

    semantics.get_symbol('reverse')
    node_symbol = semantics.get_symbol('node')
    a_symbol = semantics.get_symbol('a')
    b_symbol = semantics.get_symbol('b')
    next_symbol = semantics.get_symbol('next')
    top_sort = semantics.get_sort('SortGeneratedTopCell').aml_symbol
    semantics.get_sort('SortTree').aml_symbol

    # Rewrite rule
    # #next => reverse(node(b, a))
    next_to_reverse = semantics.get_axiom(1)
    assert isinstance(next_to_reverse, KRewritingRule)

    # Function rules
    # reverse(node(T1, T2)) = node(reverse(T2), reverse(T1))
    rec_case = semantics.get_axiom(4)
    assert isinstance(rec_case, KEquationalRule)
    # reverse(b) = b
    base_case_b = semantics.get_axiom(3)
    assert isinstance(base_case_b, KEquationalRule)
    # reverse(a) = a
    base_case_a = semantics.get_axiom(2)
    assert isinstance(base_case_a, KEquationalRule)

    initial_subterm = next_symbol.app()
    initial_config = tree_semantics_config_pattern(semantics, 'SortTree', initial_subterm)

    final_subterm = node_symbol.app(b_symbol.app(), a_symbol.app())
    final_config = tree_semantics_config_pattern(semantics, 'SortTree', final_subterm)

    claim = kore_rewrites(top_sort, initial_config, final_config)

    # Create an instance of the class
    proof_expr = ExecutionProofExp(semantics, init_config=initial_config)

    # Make the first rewrite step
    proof_expr.rewrite_event(next_to_reverse, {})

    # Make the simplifications
    proof_expr.simplification_event(rec_case.ordinal, {1: a_symbol.app(), 2: b_symbol.app()}, (0, 0, 0))
    proof_expr.simplification_event(base_case_b.ordinal, {}, (0,))
    proof_expr.simplification_event(base_case_a.ordinal, {}, (1,))

    # Test generating proofs function
    assert proof_expr._claims[0] == claim, proof_expr.pretty_diff(claim, proof_expr._claims[0])
    assert [p.conc for p in proof_expr._proof_expressions][0] == claim, proof_expr.pretty_diff(
        claim, [p.conc for p in proof_expr._proof_expressions][0]
    )


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
    complete_hints = hints_builder()
    hints: list[RewriteStepExpression] = [hint[0] for hint in complete_hints]
    initial_config = complete_hints[0][1]

    # Create an instance of the class
    proof_expr = ExecutionProofExp(semantics, init_config=initial_config)
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


def test_performer_get_subterm():
    semantics = node_tree()
    reverse_symbol = semantics.get_symbol('reverse')
    node_symbol = semantics.get_symbol('node')
    a_symbol = semantics.get_symbol('a')
    b_symbol = semantics.get_symbol('b')

    intermidiate_config = tree_semantics_config_pattern(
        semantics,
        'SortTree',
        reverse_symbol.app(node_symbol.app(a_symbol.app(), b_symbol.app())),
    )

    subpattern1 = reverse_symbol.app(node_symbol.app(a_symbol.app(), b_symbol.app()))
    subpattern2 = node_symbol.app(a_symbol.app(), b_symbol.app())
    subpattern3 = a_symbol.app()
    subpattern4 = b_symbol.app()

    performer = SimplificationPerformer(semantics, DummyProver(semantics), intermidiate_config)
    # generated_top (ignored) -> k -> inj -> ksym_reverse(node(a, b))
    assert performer.get_subterm((0, 0, 0), intermidiate_config) == subpattern1
    # ksym_reverse -> node(a, b)
    assert performer.get_subterm((0,), subpattern1) == subpattern2
    # ksym_reverse -> node -> a
    assert performer.get_subterm((0, 0), subpattern1) == subpattern3
    # ksym_reverse -> node -> b
    assert performer.get_subterm((0, 1), subpattern1) == subpattern4


def test_performer_update_subterm():
    # Semantics and symbols
    semantics = node_tree()
    reverse_symbol = semantics.get_symbol('reverse')
    node_symbol = semantics.get_symbol('node')
    a_symbol = semantics.get_symbol('a')
    b_symbol = semantics.get_symbol('b')

    # Build the initial state
    initial_kcell_value = reverse_symbol.app(node_symbol.app(a_symbol.app(), b_symbol.app()))
    intermidiate_config = tree_semantics_config_pattern(
        semantics,
        'SortTree',
        initial_kcell_value,
    )

    # Create the performer
    performer = SimplificationPerformer(semantics, DummyProver(semantics), intermidiate_config)

    # Test from the get_subpattern function
    # generated_top (ignored) -> k -> inj -> ksym_reverse(node(a, b))
    location = (0, 0, 0)
    pattern = intermidiate_config
    plug = a_symbol.app()
    expected_result = tree_semantics_config_pattern(semantics, 'SortTree', plug)
    assert performer.update_subterm(location, pattern, plug) == expected_result

    # Update tge subpattern for the whole configuration
    # ksym_generated_top -> ksym_k -> ksym_inj -> ksym_node -> ksym_reverse -> ksym_b
    location = (0, 0, 0, 1)
    plug = a_symbol.app()
    pattern = tree_semantics_config_pattern(
        semantics,
        'SortTree',
        node_symbol.app(reverse_symbol.app(a_symbol.app()), reverse_symbol.app(b_symbol.app())),
    )
    result = tree_semantics_config_pattern(
        semantics,
        'SortTree',
        node_symbol.app(reverse_symbol.app(a_symbol.app()), a_symbol.app()),
    )
    assert performer.update_subterm(location, pattern, plug) == result

    # Update the subpattern for a subterm without cells
    # node -> ksym_reverse
    location = (1,)
    pattern = node_symbol.app(reverse_symbol.app(a_symbol.app()), reverse_symbol.app(b_symbol.app()))
    plug = b_symbol.app()
    result = node_symbol.app(reverse_symbol.app(a_symbol.app()), b_symbol.app())
    assert performer.update_subterm(location, pattern, plug) == result


def test_performer_apply_substitution():
    semantics = node_tree()
    reverse_symbol = semantics.get_symbol('reverse')
    node_symbol = semantics.get_symbol('node')
    a_symbol = semantics.get_symbol('a')
    b_symbol = semantics.get_symbol('b')

    rule = semantics.get_axiom(4)
    assert isinstance(rule, KEquationalRule)
    substitution = {1: a_symbol.app(), 2: b_symbol.app()}
    expected = node_symbol.app(reverse_symbol.app(b_symbol.app()), reverse_symbol.app(a_symbol.app()))
    substtuted = rule.right.apply_esubsts(substitution)
    assert substtuted == expected

    rule = semantics.get_axiom(2)
    assert isinstance(rule, KEquationalRule)
    base_simplifications = rule.substitutions_from_requires
    expected = a_symbol.app()
    substituted = rule.right.apply_esubsts(base_simplifications)
    assert substituted == expected


def test_performer_update_config():
    semantics = node_tree()
    reverse_symbol = semantics.get_symbol('reverse')
    node_symbol = semantics.get_symbol('node')
    a_symbol = semantics.get_symbol('a')
    b_symbol = semantics.get_symbol('b')

    intermidiate_config1 = tree_semantics_config_pattern(
        semantics,
        'SortTree',
        reverse_symbol.app(a_symbol.app()),
    )
    intermidiate_config2 = tree_semantics_config_pattern(
        semantics,
        'SortTree',
        reverse_symbol.app(node_symbol.app(a_symbol.app(), b_symbol.app())),
    )

    performer = SimplificationPerformer(semantics, DummyProver(semantics), intermidiate_config1)
    assert performer.simplified_configuration == intermidiate_config1

    # Update the configuration
    performer.update_configuration(intermidiate_config2)
    assert performer.simplified_configuration == intermidiate_config2

    # Reset the state
    performer = SimplificationPerformer(semantics, DummyProver(semantics), intermidiate_config1)
    performer.enter_context((0, 0, 0))
    performer.apply_simplification(2, {})
    with pytest.raises(AssertionError):
        performer.update_configuration(intermidiate_config1)
    performer.exit_context()

    # But it is possible to update the configuration after the simplification
    simple_config_before = tree_semantics_config_pattern(semantics, 'SortTree', reverse_symbol.app(a_symbol.app()))
    simple_config_after = tree_semantics_config_pattern(semantics, 'SortTree', a_symbol.app())
    performer = SimplificationPerformer(semantics, DummyProver(semantics), simple_config_before)
    performer.enter_context((0, 0, 0))
    performer.apply_simplification(2, {})  # reverse(a) -> a
    performer.exit_context()
    assert performer._simplification_stack == []
    assert performer.simplified_configuration == simple_config_after

    # Update the config after simplification
    performer.update_configuration(intermidiate_config1)
    assert performer.simplified_configuration == intermidiate_config1


def test_trivial_proof() -> None:
    semantics = node_tree()
    top_sort = semantics.get_sort('SortGeneratedTopCell').aml_symbol
    tree_sort = semantics.get_sort('SortTree').aml_symbol
    reverse_symbol = semantics.get_symbol('reverse')
    a_symbol = semantics.get_symbol('a')

    config = tree_semantics_config_pattern(
        semantics,
        'SortTree',
        reverse_symbol.app(a_symbol.app()),
    )

    prover = SimplificationProver(semantics)
    proof = prover.trivial_proof(config)
    assert proof(BasicInterpreter(phase=ExecutionPhase.Proof)).conclusion == kore_equals(
        top_sort, top_sort, config, config
    )

    expression = reverse_symbol.app(a_symbol.app())
    proof = prover.trivial_proof(expression)
    assert proof(BasicInterpreter(phase=ExecutionPhase.Proof)).conclusion == kore_equals(
        tree_sort, top_sort, expression, expression
    )


@pytest.mark.parametrize(
    'prover',
    [
        DummyProver,
        SimplificationProver,
    ],
)
def test_subpattern_batch(prover: type[SimplificationProver]) -> None:
    semantics = node_tree()
    simpl_prover = prover(semantics)
    isinstance(simpl_prover, SimplificationProver)

    def eq_stackinfo(received_info: SimplificationInfo, expected_info: SimplificationInfo) -> bool:
        # Simplifies debugging
        assert received_info.proof.conc == expected_info.proof.conc, simpl_prover.pretty_diff(
            expected_info.proof.conc, received_info.proof.conc
        )
        return received_info == expected_info

    reverse_symbol = semantics.get_symbol('reverse')
    node_symbol = semantics.get_symbol('node')
    a_symbol = semantics.get_symbol('a')
    b_symbol = semantics.get_symbol('b')
    top_sort = semantics.configuration_sort
    tree_sort = semantics.get_sort('SortTree').aml_symbol

    # Rules
    # reverse(node(T1, T2)) = node(reverse(T2), reverse(T1))
    rec_case = semantics.get_axiom(4)
    assert isinstance(rec_case, KEquationalRule)
    # reverse(b) = b
    base_case_b = semantics.get_axiom(3)
    assert isinstance(base_case_b, KEquationalRule)
    # reverse(a) = a
    base_case_a = semantics.get_axiom(2)
    assert isinstance(base_case_a, KEquationalRule)

    initial_subterm = reverse_symbol.app(node_symbol.app(a_symbol.app(), b_symbol.app()))
    initial_config = tree_semantics_config_pattern(semantics, 'SortTree', initial_subterm)

    def kequals(phi0, phi1):
        return kore_equals(tree_sort, top_sort, phi0, phi1)

    performer = SimplificationPerformer(semantics, simpl_prover, initial_config)
    location = (0, 0, 0)
    performer.enter_context(location)
    performer.apply_simplification(rec_case.ordinal, {1: a_symbol.app(), 2: b_symbol.app()})
    performer.exit_context()
    expected_stack = [
        SimplificationInfo(
            location,
            initial_subterm,
            node_symbol.app(
                reverse_symbol.app(b_symbol.app()),
                reverse_symbol.app(a_symbol.app()),
            ),
            2,
            make_pt(
                kequals(
                    initial_subterm,
                    node_symbol.app(
                        reverse_symbol.app(b_symbol.app()),
                        reverse_symbol.app(a_symbol.app()),
                    ),
                )
            ),
        )
    ]
    # Direct comparison doesn't work anymore because of added proof thunks
    assert len(performer._simplification_stack) == len(expected_stack)
    assert eq_stackinfo(performer._simplification_stack[-1], expected_stack[-1])

    performer.enter_context((0,))
    expected_stack = expected_stack + [
        SimplificationInfo(
            (0,),
            reverse_symbol.app(b_symbol.app()),
            reverse_symbol.app(b_symbol.app()),
            0,
            make_pt(kequals(reverse_symbol.app(b_symbol.app()), reverse_symbol.app(b_symbol.app()))),
        )
    ]
    performer.apply_simplification(base_case_b.ordinal, {})
    expected_stack.pop()
    expected_stack = expected_stack + [
        SimplificationInfo(
            (0,),
            reverse_symbol.app(b_symbol.app()),
            b_symbol.app(),
            0,
            make_pt(kequals(reverse_symbol.app(b_symbol.app()), b_symbol.app())),
        )
    ]
    assert eq_stackinfo(performer._simplification_stack[-1], expected_stack[-1])
    performer.exit_context()
    expected_stack = [
        SimplificationInfo(
            location,
            initial_subterm,
            node_symbol.app(
                b_symbol.app(),
                reverse_symbol.app(a_symbol.app()),
            ),
            1,
            make_pt(
                kequals(
                    initial_subterm,
                    node_symbol.app(
                        b_symbol.app(),
                        reverse_symbol.app(a_symbol.app()),
                    ),
                )
            ),
        )
    ]
    assert len(performer._simplification_stack) == len(expected_stack)
    assert eq_stackinfo(performer._simplification_stack[-1], expected_stack[-1])

    performer.enter_context((1,))
    expected_stack = expected_stack + [
        SimplificationInfo(
            (1,),
            reverse_symbol.app(a_symbol.app()),
            reverse_symbol.app(a_symbol.app()),
            0,
            make_pt(kequals(reverse_symbol.app(a_symbol.app()), reverse_symbol.app(a_symbol.app()))),
        )
    ]
    performer.apply_simplification(base_case_a.ordinal, {})
    expected_stack.pop()
    expected_stack = expected_stack + [
        SimplificationInfo(
            (1,),
            reverse_symbol.app(a_symbol.app()),
            a_symbol.app(),
            0,
            make_pt(kequals(reverse_symbol.app(a_symbol.app()), a_symbol.app())),
        )
    ]
    performer.exit_context()
    assert performer._simplification_stack == []

    # Check the final update of the configuration
    simplified_subterm = node_symbol.app(b_symbol.app(), a_symbol.app())
    assert performer.simplified_configuration == tree_semantics_config_pattern(
        semantics, 'SortTree', simplified_subterm
    )

    # Check proof
    assert isinstance(performer.proof, ProofThunk)
    assert performer.proof.conc
    _, _, left, right = kore_equals.assert_matches(performer.proof.conc)
    assert left == initial_subterm
    assert right == simplified_subterm


def test_prove_equality_from_rule() -> None:
    semantics = node_tree()
    a_symbol = semantics.get_symbol('a')
    b_symbol = semantics.get_symbol('b')
    node_symbol = semantics.get_symbol('node')
    reverse_symbol = semantics.get_symbol('reverse')
    tree_sort = semantics.get_sort('SortTree').aml_symbol
    outer_sort = semantics.configuration_sort.aml_symbol

    # Create a new proof expression
    proof_expr = SimplificationProver(semantics)

    # reverse(a) = a
    base_case_a = semantics.get_axiom(2)
    assert isinstance(base_case_a, KEquationalRule)
    rule_with_substitution = base_case_a.pattern.apply_esubsts({0: a_symbol.app(), 1: a_symbol.app()})

    rule_proof_thunk = make_pt(rule_with_substitution)
    expected_equation = kore_equals(tree_sort, outer_sort, reverse_symbol.app(a_symbol.app()), a_symbol.app())
    equation_proof = proof_expr.prove_equality_from_rule(rule_proof_thunk)
    assert equation_proof(BasicInterpreter(phase=ExecutionPhase.Proof)).conclusion == expected_equation

    # reverse(b) = b
    base_case_b = semantics.get_axiom(3)
    assert isinstance(base_case_b, KEquationalRule)
    rule_with_substitution = base_case_b.pattern.apply_esubsts({0: b_symbol.app(), 1: b_symbol.app()})

    rule_proof_thunk = make_pt(rule_with_substitution)
    expected_equation = kore_equals(tree_sort, outer_sort, reverse_symbol.app(b_symbol.app()), b_symbol.app())
    equation_proof = proof_expr.prove_equality_from_rule(rule_proof_thunk)
    assert equation_proof(BasicInterpreter(phase=ExecutionPhase.Proof)).conclusion == expected_equation

    # reverse(node(T1, T2)) = node(reverse(T2), reverse(T1))
    rec_case = semantics.get_axiom(4)
    assert isinstance(rec_case, KEquationalRule)
    node_a_b_subterm = node_symbol.app(a_symbol.app(), b_symbol.app())
    rule_with_substitution = rec_case.pattern.apply_esubsts({0: node_a_b_subterm, 1: a_symbol.app(), 2: b_symbol.app()})

    rule_proof_thunk = make_pt(rule_with_substitution)
    expected_equation = kore_equals(
        tree_sort,
        outer_sort,
        reverse_symbol.app(node_a_b_subterm),
        node_symbol.app(reverse_symbol.app(b_symbol.app()), reverse_symbol.app(a_symbol.app())),
    )
    equation_proof = proof_expr.prove_equality_from_rule(rule_proof_thunk)
    assert equation_proof(BasicInterpreter(phase=ExecutionPhase.Proof)).conclusion == expected_equation

    # Same but with a rule with partial substitution
    node_subterm = node_symbol.app(EVar(1), EVar(2))
    rule_with_substitution = rec_case.pattern.apply_esubsts({0: node_subterm})

    rule_proof_thunk = make_pt(rule_with_substitution)
    expected_equation = kore_equals(
        tree_sort,
        outer_sort,
        reverse_symbol.app(node_subterm),
        node_symbol.app(reverse_symbol.app(EVar(2)), reverse_symbol.app(EVar(1))),
    )
    equation_proof = proof_expr.prove_equality_from_rule(rule_proof_thunk)
    assert equation_proof(BasicInterpreter(phase=ExecutionPhase.Proof)).conclusion == expected_equation


def test_apply_framing_lemma() -> None:
    semantics = node_tree()
    semantics = node_tree()
    tree_sort = semantics.get_sort('SortTree').aml_symbol
    reverse_symbol = semantics.get_symbol('reverse')
    node_symbol = semantics.get_symbol('node')
    a_symbol = semantics.get_symbol('a')
    b_symbol = semantics.get_symbol('b')

    expression1 = reverse_symbol.app(node_symbol.app(a_symbol.app(), b_symbol.app()))
    expression2 = node_symbol.app(reverse_symbol.app(b_symbol.app()), reverse_symbol.app(a_symbol.app()))
    configuration_hole = tree_semantics_config_pattern(semantics, 'SortTree', HOLE)

    config1 = tree_semantics_config_pattern(semantics, 'SortTree', expression1)
    config2 = tree_semantics_config_pattern(semantics, 'SortTree', expression2)

    equality_pt = make_pt(kore_equals(tree_sort, tree_sort, expression1, expression2))
    exprected_result = make_pt(kore_equals(tree_sort, tree_sort, config1, config2))

    prover = SimplificationProver(semantics)
    proof = prover.apply_framing_lemma(equality_pt, configuration_hole)

    # Check the logic of the prover and the dummy prover
    dummy_proof = DummyProver(semantics).apply_framing_lemma(equality_pt, configuration_hole)
    assert dummy_proof.conc == exprected_result.conc
    assert dummy_proof.conc == proof.conc

    # Check the proof with the basic interpreter
    assert proof(BasicInterpreter(phase=ExecutionPhase.Proof)).conclusion == exprected_result.conc


def test_equality_proof() -> None:
    semantics = node_tree()
    a_symbol = semantics.get_symbol('a')
    b_symbol = semantics.get_symbol('b')
    node_symbol = semantics.get_symbol('node')
    reverse_symbol = semantics.get_symbol('reverse')
    tree_sort = semantics.get_sort('SortTree').aml_symbol
    outer_sort = semantics.configuration_sort.aml_symbol

    # Create a new proof expression
    proof_expr = SimplificationProver(semantics)

    # reverse(a) = a
    base_case_a = semantics.get_axiom(2)
    base_substitutions: dict[int, Pattern] = {0: a_symbol.app(), 1: a_symbol.app()}
    main_substitutions: dict[int, Pattern] = {}
    assert isinstance(base_case_a, KEquationalRule)

    expected_equation = kore_equals(tree_sort, outer_sort, reverse_symbol.app(a_symbol.app()), a_symbol.app())
    proof = proof_expr.equality_proof(base_case_a.pattern, base_substitutions, main_substitutions)
    dummy_proof = DummyProver(semantics).equality_proof(base_case_a.pattern, base_substitutions, main_substitutions)
    assert dummy_proof.conc == expected_equation
    assert dummy_proof.conc == proof.conc
    assert proof(BasicInterpreter(phase=ExecutionPhase.Proof)).conclusion == expected_equation

    # reverse(node(T1, T2)) = node(reverse(T2), reverse(T1))
    rec_case = semantics.get_axiom(4)
    assert isinstance(rec_case, KEquationalRule)
    node_subterm = node_symbol.app(EVar(1), EVar(2))
    base_substitutions = {0: node_subterm}
    main_substitutions = {1: a_symbol.app(), 2: b_symbol.app()}

    expected_equation = kore_equals(
        tree_sort,
        outer_sort,
        reverse_symbol.app(node_symbol.app(a_symbol.app(), b_symbol.app())),
        node_symbol.app(reverse_symbol.app(b_symbol.app()), reverse_symbol.app(a_symbol.app())),
    )
    proof = proof_expr.equality_proof(rec_case.pattern, base_substitutions, main_substitutions)
    dummy_proof = DummyProver(semantics).equality_proof(rec_case.pattern, base_substitutions, main_substitutions)
    assert dummy_proof.conc == expected_equation
    assert dummy_proof.conc == proof.conc
    assert proof(BasicInterpreter(phase=ExecutionPhase.Proof)).conclusion == expected_equation


def test_equality_transitivity() -> None:
    semantics = node_tree()
    tree_sort = semantics.get_sort('SortTree').aml_symbol
    reverse_symbol = semantics.get_symbol('reverse')
    node_symbol = semantics.get_symbol('node')
    a_symbol = semantics.get_symbol('a')
    b_symbol = semantics.get_symbol('b')

    expression1 = reverse_symbol.app(node_symbol.app(a_symbol.app(), b_symbol.app()))
    expression3 = node_symbol.app(reverse_symbol.app(b_symbol.app()), reverse_symbol.app(a_symbol.app()))
    expression2 = node_symbol.app(b_symbol.app(), a_symbol.app())

    prover = SimplificationProver(semantics)

    proof1 = make_pt(kore_equals(tree_sort, tree_sort, expression1, expression2))
    proof2 = make_pt(kore_equals(tree_sort, tree_sort, expression2, expression3))
    exprected_result = make_pt(kore_equals(tree_sort, tree_sort, expression1, expression3))

    proof = prover.equality_transitivity(proof1, proof2)

    # Check the logic of the prover and the dummy prover
    dummy_proof = DummyProver(semantics).equality_transitivity(proof1, proof2)
    assert dummy_proof.conc == exprected_result.conc
    assert dummy_proof.conc == proof.conc

    # Check the proof with the basic interpreter
    assert proof(BasicInterpreter(phase=ExecutionPhase.Proof)).conclusion == exprected_result.conc


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
    rhs_with_ensures1 = kore_and(right1, ensures1)
    equation_pattern1 = kore_implies(
        sort1.aml_symbol, requires1, kore_equals(sort1.aml_symbol, sort1.aml_symbol, left1, rhs_with_ensures1)
    )

    requires2 = kore_top(sort2.aml_symbol)
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
