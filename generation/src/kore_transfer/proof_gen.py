from __future__ import annotations

from argparse import ArgumentParser
from pathlib import Path
from typing import TYPE_CHECKING

import pyk.kllvm.load  # noqa: F401
from pyk.kore.kompiled import KompiledKore
from pyk.ktool.kompile import kompile

from kore_transfer.execution_proof_generation import generate_proofs
from kore_transfer.kore_convertion.language_semantics import LanguageSemantics
from kore_transfer.kore_convertion.rewrite_steps import get_proof_hints
from proof_generation.llvm_proof_hint import LLVMRewriteTrace

if TYPE_CHECKING:
    from pyk.kore.syntax import Axiom, Definition

    from proof_generation.proof import ProofExp


def get_kompiled_definition(output_dir: Path) -> Definition:
    print(f'Parsing the definition in the Kore format in {output_dir}')
    return KompiledKore(output_dir).definition


def get_kompiled_dir(k_file: str, output_dir: str, reuse_kompiled_dir: bool = False) -> Path:
    """Kompile given K definition and return path to the kompiled directory."""

    path = Path(output_dir)
    if reuse_kompiled_dir and path.exists() and path.is_dir():
        print(f'Using existing kompiled directory {path}')
        return Path(path)
    elif reuse_kompiled_dir:
        print(f'Kompiled directory {path} does not exist. Compiling from scratch.')

    print(f'Kompiling target {k_file} to {output_dir}')
    kompiled_dir: Path = kompile(main_file=k_file, backend='llvm', output_dir=output_dir)
    return kompiled_dir


def generate_proof_file(proof_gen: ProofExp, output_dir: Path, file_name: str, pretty: bool = False) -> None:
    """Generate the proof files."""
    if not output_dir.exists():
        output_dir.mkdir(parents=True)
    mode = 'pretty' if pretty else 'binary'
    proof_gen.main(['', mode, str(output_dir), file_name])


HINTS_DIR_PATH = 'proof-hints'


def read_proof_hint(filepath: str) -> LLVMRewriteTrace:
    hint_bin = Path(filepath).read_bytes()
    return LLVMRewriteTrace.parse(hint_bin)


def get_all_axioms(kore_definition: Definition) -> list[Axiom]:
    axioms = []
    for module in kore_definition.modules:
        for axiom in module.axioms:
            axioms.append(axiom)
    return axioms


def main(
    k_file: str,
    hints_file: str,
    output_dir: str,
    proof_dir: str,
    pretty: bool = False,
    reuse_kompiled_dir: bool = False,
) -> None:
    # Kompile sources
    kompiled_dir: Path = get_kompiled_dir(k_file, output_dir, reuse_kompiled_dir)
    kore_definition = get_kompiled_definition(kompiled_dir)

    print('Begin converting ... ')
    language_definition = LanguageSemantics.from_kore_definition(kore_definition)

    # print('Intialize hint stream ... ')
    hints_iterator = get_proof_hints(read_proof_hint(hints_file), language_definition)

    print('Begin generating proofs ... ')
    kore_def = generate_proofs(hints_iterator, language_definition)
    generate_proof_file(kore_def, Path(proof_dir), Path(k_file).stem)
    print('Done!')


if __name__ == '__main__':
    argparser = ArgumentParser()
    argparser.add_argument('kfile', type=str, help='Path to the K definition file')
    argparser.add_argument('hints', type=str, help='Path to the binary hints file')
    argparser.add_argument('output_dir', type=str, help='Path to the output directory')
    argparser.add_argument(
        '--pretty',
        action='store_true',
        default=False,
        help='Print the pretty-printed version of proofs instead of the binary ones',
    )
    argparser.add_argument('--reuse', action='store_true', default=False, help='Reuse the existing kompiled directory')
    argparser.add_argument('--proof-dir', type=str, default=str(Path.cwd()), help='Output directory for saving proofs')

    args = argparser.parse_args()
    main(args.kfile, args.hints, args.output_dir, args.proof_dir, args.pretty, args.reuse)
