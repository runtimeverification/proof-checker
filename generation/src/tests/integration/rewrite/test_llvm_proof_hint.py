import os
from pathlib import Path

import pyk.kllvm.load  # noqa: F401

from proof_generation.llvm_proof_hint import LLVMRewriteTrace

HINTS_DIR_PATH = 'proof-hints'


def read_proof_hint(filepath: str) -> LLVMRewriteTrace:
    hint_bin = Path(os.path.join(HINTS_DIR_PATH, filepath)).read_bytes()
    return LLVMRewriteTrace.parse(hint_bin)


def test_parse_proof_hint_single_rewrite() -> None:
    hint = read_proof_hint('single-rewrite/foo-a.single-rewrite.hints')

    # A single rewrite step
    assert len(hint.trace) == 1

    # Contents of the k cell in the initial configuration
    k_cell = hint.initial_config.patterns[0].dict['args'][0]
    assert k_cell['name'] == 'kseq'
    assert k_cell['args'][0]['args'][0]['name'] == "LblFooA'LParRParUnds'SINGLE-REWRITE-SYNTAX'Unds'Foo"
    assert k_cell['args'][1]['name'] == 'dotk'

    # Rule applied in the single rewrite step
    assert hint.trace[0].rule_ordinal == 92

    # Contents of the k cell in the final configuration
    k_cell = hint.trace[0].post_config.patterns[0].dict['args'][0]
    assert k_cell['name'] == 'kseq'
    assert k_cell['args'][0]['args'][0]['name'] == "LblFooB'LParRParUnds'SINGLE-REWRITE-SYNTAX'Unds'Foo"
    assert k_cell['args'][1]['name'] == 'dotk'


def test_parse_proof_hint_trivial() -> None:
    names = ['0_rewrites.trivial', '1_rewrite.trivial', '2_rewrites.trivial']
    hints = [read_proof_hint('trivial/' + name + '.hints') for name in names]

    for i in range(len(hints)):
        assert len(hints[i].trace) == i


def test_parse_proof_hint_peano() -> None:
    hint = read_proof_hint('peano/mul_3_5.peano.hints')

    assert len(hint.trace) == 58


def test_parse_proof_hint_imp5() -> None:
    hint = read_proof_hint('imp5/empty.imp5.hints')

    assert len(hint.trace) == 1
