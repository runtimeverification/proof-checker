from __future__ import annotations

from argparse import ArgumentParser
from pathlib import Path
from typing import TYPE_CHECKING

from pyk.kore.kompiled import KompiledKore
from pyk.kore.parser import KoreParser
from pyk.ktool.kompile import kompile
from pyk.ktool.krun import KRunOutput, _krun

from kore_transfer.proof_gen import ExecutionProofGen

if TYPE_CHECKING:
    from pyk.kore.syntax import Definition, Pattern

    from proof_generation.proof import ProofExp


def get_kompiled_definition(output_dir: Path) -> Definition:
    """Parse the definition.kore file and return corresponding object."""

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


def get_confguration_for_depth(definition_dir: Path, input_file: Path, depth: int) -> Pattern:
    """Generate the configuration for the given depth."""

    # TODO: This can be also done using KAST and then using the KRun class but it soesn't seem easier to me
    finished_process = _krun(input_file=input_file, definition_dir=definition_dir, output=KRunOutput.KORE, depth=depth)
    # TODO: We can consider implementing a better error handling
    assert finished_process.returncode == 0, 'KRun failed'

    parsed = KoreParser(finished_process.stdout)
    return parsed.pattern()


def generate_proof_file(proof_gen: type[ProofExp], output_dir: Path, file_name: str) -> None:
    """Generate the proof files."""
    if not output_dir.exists():
        output_dir.mkdir(parents=True)
    proof_gen.main(['', 'binary', 'gamma', str(output_dir / f'{file_name}.ml-gamma')])
    proof_gen.main(['', 'binary', 'claim', str(output_dir / f'{file_name}.ml-claim')])
    proof_gen.main(['', 'binary', 'proof', str(output_dir / f'{file_name}.ml-proof')])


def main(
    k_file: str,
    module_name: str | None,
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
    configuration_for_step = get_confguration_for_depth(kompiled_dir, Path(program_file), step)
    configuration_for_next_step = get_confguration_for_depth(kompiled_dir, Path(program_file), step + 1)

    # Find the module name
    assert len(kore_definition.modules) > 0, 'Empty K definition'
    if not module_name:
        module_name = kore_definition.modules[-1].name

    print('Begin converting ... ')
    converter = ExecutionProofGen(kore_definition, module_name)
    converter.prove_rewrite_step(configuration_for_step, configuration_for_next_step)
    proof_gen_class = converter.compose_proofs()

    print('Begin generating proof files ... ')
    generate_proof_file(proof_gen_class, output_proof_dir, Path(k_file).stem)

    print('Done!')


if __name__ == '__main__':
    argparser = ArgumentParser()
    argparser.add_argument('kfile', type=str, help='Path to the K definition file')
    argparser.add_argument('program', type=str, help='Path to the program file')
    argparser.add_argument('output_dir', type=str, help='Path to the output directory')
    argparser.add_argument('--module', type=str, help='Main K module name')
    argparser.add_argument('--depth', type=int, default=0, help='Execution steps from the beginning')
    argparser.add_argument('--reuse', action='store_true', default=False, help='Reuse the existing kompiled directory')
    argparser.add_argument('--clean', action='store_true', default=False, help='Rewrite proofs if they already exist')
    argparser.add_argument('--proof-dir', type=str, default=str(Path.cwd()), help='Output directory for saving proofs')

    args = argparser.parse_args()
    main(args.kfile, args.module, args.program, args.output_dir, args.proof_dir, args.depth, args.reuse, args.clean)
