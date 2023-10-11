from pathlib import Path

import pyk.kllvm.load  # noqa: F401

from rewrite.llvm_proof_hint import LLVMRewriteTrace


def test_parse_proof_hint() -> None:
    bin_hint = Path('proof-hints/proof-hints.bin').read_bytes()
    hint = LLVMRewriteTrace.parse(bin_hint)
    assert len(hint.trace) == 64
    # TODO: Strenghten these assertions.
