from __future__ import annotations

from pytest import fixture

from proof_generation.k.execution_proof_generation import ExecutionProofExp, generate_proofs
from proof_generation.k.kore_convertion.language_semantics import LanguageSemantics
from proof_generation.k.kore_convertion.rewrite_steps import RewriteStepExpression
from proof_generation.proofs.kore import kore_rewrites


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

            rewrite_rule1 = mod.rewrite_rule(
                kore_rewrites(sort.aml_symbol, a_symbol.aml_notation(), b_symbol.aml_notation())
            )
            rewrite_rule2 = mod.rewrite_rule(
                kore_rewrites(sort.aml_symbol, b_symbol.aml_notation(), c_symbol.aml_notation())
            )

    # Construct RewriteStepExpression
    step_one = RewriteStepExpression(
        a_symbol.aml_notation(),
        (),
        b_symbol.aml_notation(),
        rewrite_rule1,
        {},
    )
    step_two = RewriteStepExpression(
        b_symbol.aml_notation(),
        (),
        c_symbol.aml_notation(),
        rewrite_rule2,
        {},
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
