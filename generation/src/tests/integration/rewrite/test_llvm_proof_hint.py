import os
from pathlib import Path

import pyk.kllvm.load  # noqa: F401
import pyk.kore.syntax as kore

from proof_generation.llvm_proof_hint import LLVMRewriteTrace, LLVMRuleEvent

HINTS_DIR_PATH = 'proof-hints'


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
