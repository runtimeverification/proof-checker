from __future__ import annotations

import subprocess
from pathlib import Path
from typing import TYPE_CHECKING

import pyk.kllvm.load  # noqa: F401

from proof_generation.aml import App, Instantiate, Symbol
from proof_generation.k.kore_convertion.language_semantics import LanguageSemantics
from proof_generation.k.kore_convertion.rewrite_steps import get_proof_hints
from proof_generation.k.proof_gen import get_kompiled_definition, read_proof_hint

if TYPE_CHECKING:
    from collections.abc import Iterator

    from proof_generation.aml import Pattern
    from proof_generation.k.kore_convertion.rewrite_steps import RewriteStepExpression


HINTS_DIR = '.build/proof-hints'
K_BENCHMARKS_DIR = 'generation/k-benchmarks'
KOMPILED_DIR = '.build/kompiled-definitions'


def get_k_cell_top_symbol(term: Pattern) -> Pattern:
    if isinstance(term, Instantiate):
        term = term.simplify()
    assert isinstance(term, App)
    term = term.left
    assert isinstance(term, App)
    term = term.right
    if isinstance(term, Instantiate):
        term = term.simplify()
    assert isinstance(term, App)
    term = term.right
    if isinstance(term, Instantiate):
        term = term.simplify()
    assert isinstance(term, App)
    term = term.left
    assert isinstance(term, App)
    term = term.right
    if isinstance(term, Instantiate):
        term = term.simplify()
    assert isinstance(term, App)
    term = term.right
    if isinstance(term, Instantiate):
        term = term.simplify()
    return term


def generate_proof_trace(
    k_file: Path,
    hints_file: Path,
    kompiled_dir: Path,
) -> tuple[Pattern, Iterator[RewriteStepExpression]]:
    # Kompile sources if needed
    if not kompiled_dir.exists():
        output = subprocess.run(
            ['kompile', '--backend', 'llvm', '--output-definition', kompiled_dir, k_file],
            capture_output=True,
            text=True,
        )
        assert output.returncode == 0, f'Kompile failed: {output.stderr}'

    # Read kompiled definition
    kore_definition = get_kompiled_definition(kompiled_dir)

    print('Begin converting ... ')
    language_definition = LanguageSemantics.from_kore_definition(kore_definition)

    # print('Intialize hint stream ... ')
    initial_config, hints_iterator = get_proof_hints(read_proof_hint(str(hints_file)), language_definition)

    return initial_config, hints_iterator


def test_proof_trace_single_rewrite() -> None:
    k_file = Path(K_BENCHMARKS_DIR + '/single-rewrite/single-rewrite.k')
    hints_file = Path(HINTS_DIR + '/single-rewrite/foo-a.single-rewrite.hints')
    kompiled_dir = Path(KOMPILED_DIR + '/single-rewrite-kompiled/')

    initial_config, iterator = generate_proof_trace(k_file, hints_file, kompiled_dir)
    assert initial_config
    assert iterator

    # Test the initial configuration
    pre_symbol = get_k_cell_top_symbol(initial_config)
    assert isinstance(pre_symbol, Symbol)
    assert pre_symbol.name == "ksym_LblFooA'LParRParUnds'SINGLE-REWRITE-SYNTAX'Unds'Foo"

    # First rewrite
    hint = next(iterator, None)
    assert hint
    assert hint.axiom.ordinal == 92
    assert len(hint.substitutions) == 2

    # No more rewrites rewrite
    assert next(iterator, None) == None


def test_proof_trace_double_rewrite() -> None:
    k_file = Path(K_BENCHMARKS_DIR + '/double-rewrite/double-rewrite.k')
    hints_file = Path(HINTS_DIR + '/double-rewrite/foo-a.double-rewrite.hints')
    kompiled_dir = Path(KOMPILED_DIR + '/double-rewrite-kompiled/')

    initial_config, iterator = generate_proof_trace(k_file, hints_file, kompiled_dir)
    assert initial_config
    assert iterator

    # Test the initial configuration
    pre_symbol = get_k_cell_top_symbol(initial_config)
    assert isinstance(pre_symbol, Symbol)
    assert pre_symbol.name == "ksym_LblFooA'LParRParUnds'DOUBLE-REWRITE-SYNTAX'Unds'Foo"

    # First rewrite
    hint = next(iterator, None)
    assert hint
    assert hint.axiom.ordinal == 95
    assert len(hint.substitutions) == 2

    # Second rewrite
    hint = next(iterator, None)
    assert hint

    assert hint.axiom.ordinal == 96
    assert len(hint.substitutions) == 2

    # No more rewrites rewrite
    assert next(iterator, None) == None
