import os
from pathlib import Path

import pyk.kllvm.load  # noqa: F401

from rewrite.llvm_proof_hint import LLVMRewriteTrace


def list_files_recursively(directory: str) -> list[str]:
    file_paths = []

    for root, _, files in os.walk(directory):
        for file in files:
            file_paths.append(os.path.join(root, file))

    return file_paths


def test_parse_proof_hint() -> None:
    hints_dir_path = 'proof-hints'
    assert os.path.exists(
        hints_dir_path
    ), 'The proof hints directory {!r} does not exist. Make sure proof hints are generated and stored in this directory before running the integration tests.'.format(
        hints_dir_path
    )

    hint_files = list_files_recursively(hints_dir_path)
    for file_path in hint_files:
        hint_name = os.path.splitext(os.path.basename(file_path))[0]
        hint_bin = Path(file_path).read_bytes()
        hint = LLVMRewriteTrace.parse(hint_bin)

        # Add example-specific testing logic here
        if hint_name == '0_rewrites.trivial':
            assert len(hint.trace) == 0

        elif hint_name == '1_rewrite.trivial':
            assert len(hint.trace) == 1

        elif hint_name == '2_rewrites.trivial':
            assert len(hint.trace) == 2

        elif hint_name == 'foo-a.single-rewrite':
            # A single rewrite step
            assert len(hint.trace) == 1

            # Contents of the k cell in the initial configuration
            p = hint.initial_config.patterns[0].args[0]  # type: ignore
            assert p.symbol == 'kseq'
            assert p.args[0].args[0].symbol == "LblFooA'LParRParUnds'SINGLE-REWRITE-SYNTAX'Unds'Foo"
            assert p.args[1].symbol == 'dotk'

            # Rule applied in the single rewrite step
            assert hint.trace[0].rule_ordinal == 92

            # Contents of the k cell in the final configuration
            p = hint.trace[0].post_config.patterns[0].args[0]  # type: ignore
            assert p.symbol == 'kseq'
            assert p.args[0].args[0].symbol == "LblFooB'LParRParUnds'SINGLE-REWRITE-SYNTAX'Unds'Foo"
            assert p.args[1].symbol == 'dotk'

        elif hint_name == 'mul_3_5.peano':
            assert len(hint.trace) == 58
