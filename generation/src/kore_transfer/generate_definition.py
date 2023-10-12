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


def get_kompiled_definition(output_dir: Path) -> Definition:
    """Parse the definition.kore file and return corresponding object."""

    print(f'Parsing the definition in the Kore format in {output_dir}')
    return KompiledKore(output_dir).definition


def get_kompiled_dir(k_file: str, output_dir: str, reuse_kompiled_dir=False) -> Path:
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


def main(k_file: str, module_name: str, program_file: str, output_dir: str, step=0, reuse_kompiled_dir=False) -> None:
    print(f'Kompiling target {k_file} to {output_dir}')
    kompiled_dir: Path = get_kompiled_dir(k_file, output_dir, reuse_kompiled_dir)
    kore_definition = get_kompiled_definition(kompiled_dir)
    configuration_pattern = get_confguration_for_depth(kompiled_dir, Path(program_file), step)

    print('Begin converting ... ')
    converter = ExecutionProofGen(kore_definition, module_name)
    converter.take_rewrite_step(configuration_pattern)

    print('Done!')


if __name__ == '__main__':
    argparser = ArgumentParser()
    argparser.add_argument('kfile', type=str, help='Path to the K definition file')
    argparser.add_argument('module', type=str, help='Main K module name')
    argparser.add_argument('program', type=str, help='Path to the program file')
    argparser.add_argument('output_dir', type=str, help='Path to the output directory')
    argparser.add_argument('--depth', type=int, default=0, help='Execution steps from the beginning')
    argparser.add_argument('--reuse', action='store_true', help='Reuse the existing kompiled directory')

    args = argparser.parse_args()
    main(args.kfile, args.module, args.program, args.output_dir, args.depth, args.reuse)
