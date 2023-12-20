import os
from pathlib import Path

import pyk.kllvm.load  # noqa: F401
import pyk.kore.syntax as kore

from proof_generation.llvm_proof_hint import LLVMFunctionEvent, LLVMRewriteTrace, LLVMRuleEvent

HINTS_DIR_PATH = '.build/proof-hints'


def read_proof_hint(filepath: str) -> LLVMRewriteTrace:
    hint_bin = Path(os.path.join(HINTS_DIR_PATH, filepath)).read_bytes()
    return LLVMRewriteTrace.parse(hint_bin)


def test_parse_proof_hint_single_rewrite() -> None:
    hint = read_proof_hint('single-rewrite/foo-a.single-rewrite.hints')

    # 11 initialization events
    assert len(hint.pre_trace) == 11

    # 2 post-initial-configuration events
    assert len(hint.trace) == 2

    # Contents of the k cell in the initial configuration
    k_cell = hint.initial_config.patterns[0].dict['args'][0]
    assert k_cell['name'] == 'kseq'
    assert k_cell['args'][0]['args'][0]['name'] == "LblFooA'LParRParUnds'SINGLE-REWRITE-SYNTAX'Unds'Foo"
    assert k_cell['args'][1]['name'] == 'dotk'

    # Rule applied in the single (non-functional) rewrite step
    rule_event = hint.trace[0]
    assert isinstance(rule_event, LLVMRuleEvent)
    assert rule_event.rule_ordinal == 92

    # Contents of the k cell in the final configuration
    final_config = hint.trace[1]
    assert isinstance(final_config, kore.Pattern)
    k_cell = final_config.patterns[0].dict['args'][0]
    assert k_cell['name'] == 'kseq'
    assert k_cell['args'][0]['args'][0]['name'] == "LblFooB'LParRParUnds'SINGLE-REWRITE-SYNTAX'Unds'Foo"
    assert k_cell['args'][1]['name'] == 'dotk'


def test_parse_proof_hint_reverse_no_ints() -> None:
    hint = read_proof_hint('tree-reverse-without-integers/simplify.tree-reverse-without-integers.hints')

    # 11 initialization events
    assert len(hint.pre_trace) == 11

    # 2 post-initial-configuration events
    assert len(hint.trace) == 10

    # Contents of the k cell in the initial configuration
    k_cell = hint.initial_config.patterns[0].dict['args'][0]
    assert k_cell['name'] == 'kseq'
    assert k_cell['args'][0]['name'] == "Lbl'Hash'Init'Unds'TREE-REVERSE-WITHOUT-INTEGERS-SYNTAX'Unds'KItem"

    # Rule applied in the single (non-functional) rewrite step
    rule_event = hint.trace[0]
    assert isinstance(rule_event, LLVMRuleEvent)
    assert rule_event.rule_ordinal == 104
    assert len(rule_event.substitution) == 1
    assert rule_event.substitution[0][0] == "Var'Unds'DotVar0"

    # Then pattern
    rule_event = hint.trace[1]
    assert isinstance(rule_event, kore.Pattern)
    k_cell = rule_event.patterns[0].dict['args'][0]
    assert k_cell['name'] == 'kseq'
    assert k_cell['args'][0]['name'] == "Lbl'Hash'next'Unds'TREE-REVERSE-WITHOUT-INTEGERS-SYNTAX'Unds'KItem"

    # Second rewrite
    rule_event = hint.trace[2]
    assert isinstance(rule_event, LLVMRuleEvent)
    assert rule_event.rule_ordinal == 105
    assert len(rule_event.substitution) == 1
    assert rule_event.substitution[0][0] == "Var'Unds'DotVar0"

    # Function event
    rule_event = hint.trace[3]
    assert isinstance(rule_event, LLVMFunctionEvent)
    assert rule_event.name == "Lblreverse'LParUndsRParUnds'TREE-REVERSE-WITHOUT-INTEGERS-SYNTAX'Unds'Tree'Unds'Tree{}"
    assert rule_event.relative_position == '0:0:0:0:0'
    assert len(rule_event.args) == 1
    assert (
        isinstance(rule_event.args[0], kore.App)
        and rule_event.args[0].symbol
        == "Lblnode'LParUndsCommUndsRParUnds'TREE-REVERSE-WITHOUT-INTEGERS-SYNTAX'Unds'Tree'Unds'Tree'Unds'Tree"
    )

    # Simplification rule
    rule_event = hint.trace[4]
    assert isinstance(rule_event, LLVMRuleEvent)
    assert rule_event.rule_ordinal == 157
    assert len(rule_event.substitution) == 2
    assert rule_event.substitution[0][0] == 'VarT1'
    assert rule_event.substitution[1][0] == 'VarT2'

    # Function event
    rule_event = hint.trace[5]
    assert isinstance(rule_event, LLVMFunctionEvent)
    assert rule_event.name == "Lblreverse'LParUndsRParUnds'TREE-REVERSE-WITHOUT-INTEGERS-SYNTAX'Unds'Tree'Unds'Tree{}"
    assert rule_event.relative_position == '0:0'
    assert len(rule_event.args) == 1
    assert (
        isinstance(rule_event.args[0], kore.App)
        and rule_event.args[0].symbol == "Lblb'Unds'TREE-REVERSE-WITHOUT-INTEGERS-SYNTAX'Unds'Tree"
    )

    # Simplification rule
    rule_event = hint.trace[6]
    assert isinstance(rule_event, LLVMRuleEvent)
    assert rule_event.rule_ordinal == 155
    assert len(rule_event.substitution) == 1
    assert rule_event.substitution[0][0] == "Var'Unds'Gen0"

    # Function event
    rule_event = hint.trace[7]
    assert isinstance(rule_event, LLVMFunctionEvent)
    assert rule_event.name == "Lblreverse'LParUndsRParUnds'TREE-REVERSE-WITHOUT-INTEGERS-SYNTAX'Unds'Tree'Unds'Tree{}"
    assert rule_event.relative_position == '0:1'
    assert len(rule_event.args) == 1
    assert (
        isinstance(rule_event.args[0], kore.App)
        and rule_event.args[0].symbol == "Lbla'Unds'TREE-REVERSE-WITHOUT-INTEGERS-SYNTAX'Unds'Tree"
    )

    # Simplification rule
    rule_event = hint.trace[8]
    assert isinstance(rule_event, LLVMRuleEvent)
    assert rule_event.rule_ordinal == 154
    assert len(rule_event.substitution) == 1
    assert rule_event.substitution[0][0] == "Var'Unds'Gen0"

    # Then pattern
    rule_event = hint.trace[9]
    assert isinstance(rule_event, kore.Pattern)
    k_cell = rule_event.patterns[0].dict['args'][0]
    assert k_cell['name'] == 'kseq'
    assert (
        k_cell['args'][0]['args'][0]['name']
        == "Lblnode'LParUndsCommUndsRParUnds'TREE-REVERSE-WITHOUT-INTEGERS-SYNTAX'Unds'Tree'Unds'Tree'Unds'Tree"
    )
    assert k_cell['args'][0]['args'][0]['args'][0]['name'] == "Lblb'Unds'TREE-REVERSE-WITHOUT-INTEGERS-SYNTAX'Unds'Tree"
    assert k_cell['args'][0]['args'][0]['args'][1]['name'] == "Lbla'Unds'TREE-REVERSE-WITHOUT-INTEGERS-SYNTAX'Unds'Tree"


def test_parse_proof_hint_trivial() -> None:
    names = ['0_rewrites.trivial', '1_rewrite.trivial', '2_rewrites.trivial']
    hints = [read_proof_hint('trivial/' + name + '.hints') for name in names]

    # 11 initialization events
    for i in range(len(hints)):
        assert len(hints[i].pre_trace) == 11

    for i in range(len(hints)):
        # a pair of (rule, config) for each non-functional rewrite step
        assert len(hints[i].trace) == i * 2


def test_parse_proof_hint_peano() -> None:
    hint = read_proof_hint('peano/mul_3_5.peano.hints')

    # 11 initialization events
    assert len(hint.pre_trace) == 11

    # 361 post-initial-configuration events
    assert len(hint.trace) == 361


def test_parse_proof_hint_imp5() -> None:
    hint = read_proof_hint('imp5/empty.imp5.hints')

    # 15 initialization events
    assert len(hint.pre_trace) == 15

    # 2 post-initial-configuration events
    assert len(hint.trace) == 2


def test_parse_proof_hint_reverse() -> None:
    hint = read_proof_hint('reverse/init.reverse.hints')

    # 11 initialization events
    assert len(hint.pre_trace) == 11

    # 10 post-initial-configuration events
    assert len(hint.trace) == 10
