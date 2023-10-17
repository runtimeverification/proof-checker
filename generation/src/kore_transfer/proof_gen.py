from __future__ import annotations

from argparse import ArgumentParser
from pathlib import Path
from typing import TYPE_CHECKING

from pyk.kore.kompiled import KompiledKore
from pyk.ktool.kompile import kompile

from kore_transfer.generate_definition import compose_definition
from kore_transfer.generate_hints import get_proof_hints
from kore_transfer.generate_proof import generate_proofs
from kore_transfer.kore_converter import KoreConverter

if TYPE_CHECKING:
    from pyk.kore.syntax import Definition

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


def generate_proof_file(proof_gen: type[ProofExp], output_dir: Path, file_name: str) -> None:
    """Generate the proof files."""
    if not output_dir.exists():
        output_dir.mkdir(parents=True)
    proof_gen.main(['', 'binary', 'gamma', str(output_dir / f'{file_name}.ml-gamma')])
    proof_gen.main(['', 'binary', 'claim', str(output_dir / f'{file_name}.ml-claim')])
    proof_gen.main(['', 'binary', 'proof', str(output_dir / f'{file_name}.ml-proof')])


def main(
    k_file: str,
    program_file: str,
    output_dir: str,
    proof_dir: str,
    step: int = 0,
    reuse_kompiled_dir: bool = False,
    rewrite_proof_files: bool = False,
) -> None:
    # First check that output directory either does not exist or can be rewritten
    output_proof_dir = Path(proof_dir)
    if output_proof_dir.exists() and not rewrite_proof_files:
        print(f'Output directory {output_proof_dir} already exists and rewrite is not allowed. Exiting.')
        return

    # Kompile sources
    kompiled_dir: Path = get_kompiled_dir(k_file, output_dir, reuse_kompiled_dir)
    kore_definition = get_kompiled_definition(kompiled_dir)

    print('Begin converting ... ')
    kore_converter = KoreConverter(kore_definition)
    proof_expression = compose_definition(kore_definition, kore_converter)

    print('Intialize hint stream ... ')
    # TODO: Fix with the real hints
    hints_iterator = get_proof_hints(kompiled_dir, Path(program_file), proof_expression, kore_converter, step)

    print('Begin generating proofs ... ')
    generate_proofs(hints_iterator, proof_expression)

    generate_proof_file(proof_expression, output_proof_dir, Path(k_file).stem)
    print('Done!')


if __name__ == '__main__':
    argparser = ArgumentParser()
    argparser.add_argument('kfile', type=str, help='Path to the K definition file')
    argparser.add_argument('program', type=str, help='Path to the program file')
    argparser.add_argument('output_dir', type=str, help='Path to the output directory')
    argparser.add_argument('--depth', type=int, default=0, help='Execution steps from the beginning')
    argparser.add_argument('--reuse', action='store_true', default=False, help='Reuse the existing kompiled directory')
    argparser.add_argument('--clean', action='store_true', default=False, help='Rewrite proofs if they already exist')
    argparser.add_argument('--proof-dir', type=str, default=str(Path.cwd()), help='Output directory for saving proofs')

    args = argparser.parse_args()
    main(args.kfile, args.program, args.output_dir, args.proof_dir, args.depth, args.reuse, args.clean)
