from __future__ import annotations

from argparse import ArgumentParser
from pathlib import Path
from typing import TYPE_CHECKING

import pyk.kllvm.load  # noqa: F401
import pyk.kore.syntax as kore
from pyk.kore.parser import KoreParser
from pyk.utils import check_file_path

from proof_generation.k.execution_proof_generation import ExecutionProofExp
from proof_generation.k.kore_convertion.language_semantics import LanguageSemantics
from proof_generation.k.kore_convertion.rewrite_steps import get_proof_hints
from proof_generation.llvm_proof_hint import LLVMRewriteTrace

if TYPE_CHECKING:
    from proof_generation.proof import ProofExp


def get_kompiled_definition(output_dir: Path) -> kore.Definition:
    print(f'Parsing the definition in the Kore format in {output_dir}')
    kore_file = output_dir / 'definition.kore'
    check_file_path(kore_file)
    kore_text = kore_file.read_text()
    return KoreParser(kore_text).definition()


def get_kompiled_dir(output_dir: str) -> Path:
    """Check that the K definition exists and return path to the kompiled directory."""

    path = Path(output_dir)
    if path.exists() and path.is_dir():
        print(f'Using existing kompiled directory {path}')
        return Path(path)
    else:
        raise AssertionError(f'Kompiled directory {path} does not exist.')


def generate_proof_file(proof_gen: ProofExp, output_dir: Path, slice_name: str, pretty_no_stack: bool = False) -> None:
    """Generate the proof files."""
    if not output_dir.exists():
        output_dir.mkdir(parents=True)
    mode = 'pretty-no-stack' if pretty_no_stack else 'binary'
    proof_gen.main(['', mode, str(output_dir), slice_name])


def read_proof_hint(filepath: str) -> LLVMRewriteTrace:
    hint_bin = Path(filepath).read_bytes()
    return LLVMRewriteTrace.parse(hint_bin)


def get_all_axioms(definition: kore.Definition) -> list[kore.Axiom]:
    axioms = []
    for module in definition.modules:
        for axiom in module.axioms:
            axioms.append(axiom)
    return axioms


def get_axiom_label(attrs: tuple[kore.App, ...]) -> str:
    for attr in attrs:
        if attr.symbol == 'label' and isinstance(attr.args[0], kore.String):
            return attr.args[0].value
    return 'N/A'


def main(
    module: str,
    hints_file: str,
    kompiled: str,
    proof_dir: str,
    pretty_no_stack: bool = False,
) -> None:
    # Kompile sources
    kompiled_dir: Path = get_kompiled_dir(kompiled)
    kore_definition = get_kompiled_definition(kompiled_dir)

    print('Begin converting ... ')
    language_semantics = LanguageSemantics.from_kore_definition(kore_definition)

    # print('Intialize hint stream ... ')
    initial_config, hints_iterator = get_proof_hints(read_proof_hint(hints_file), language_semantics)

    print('Begin generating proofs ... ')
    kore_def = ExecutionProofExp.from_proof_hints(initial_config, hints_iterator, language_semantics)
    slice_name = Path(hints_file).stem + '.' + module
    generate_proof_file(kore_def, Path(proof_dir), slice_name, pretty_no_stack)
    print('Done!')


if __name__ == '__main__':
    argparser = ArgumentParser()
    argparser.add_argument('module', type=str, help='The module name')
    argparser.add_argument('hints', type=str, help='Path to the binary hints file')
    argparser.add_argument('kompiled', type=str, help='Path to the kompiled directory')
    argparser.add_argument('--proof-dir', type=str, default=str(Path.cwd()), help='Output directory for saving proofs')
    argparser.add_argument(
        '--pretty',
        action='store_true',
        default=False,
        help='Print the pretty-printed version of proofs instead of the binary ones',
    )

    args = argparser.parse_args()
    main(args.module, args.hints, args.kompiled, args.proof_dir, args.pretty)
