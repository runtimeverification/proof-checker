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

        # Add per-test logic here
        if hint_name == '0_rewrites.trivial':
            assert len(hint.trace) == 0
        elif hint_name == '1_rewrite.trivial':
            assert len(hint.trace) == 1
        elif hint_name == '2_rewrites.trivial':
            assert len(hint.trace) == 2
        elif hint_name == 'foo-a.single-rewrite':
            assert len(hint.trace) == 1
        elif hint_name == 'mul_3_5.peano':
            assert len(hint.trace) == 58
