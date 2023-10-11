from __future__ import annotations

from argparse import ArgumentParser
from pathlib import Path
from typing import TYPE_CHECKING

from pyk.kore.kompiled import KompiledKore
from pyk.kore.parser import KoreParser
from pyk.ktool.kompile import kompile
from pyk.ktool.krun import KRunOutput, _krun

if TYPE_CHECKING:
    from pyk.kore.syntax import Definition, Pattern


def get_kompiled_definition(output_dir: Path) -> Definition:
    print(f'Parsing the definition in the Kore format in {output_dir}')
    return KompiledKore(output_dir).definition


def get_kompiled_dir(k_file: str, output_dir: str) -> Path:
    print(f'Kompiling target {k_file} to {output_dir}')
    kompiled_dir: Path = kompile(main_file=k_file, backend='llvm', output_dir=output_dir)
    return kompiled_dir


def get_confguration_for_depth(definition_dir: Path, input_file: Path, depth: int) -> Pattern:
    # TODO: This can be also done using KAST and then using the KRun class but it soesn't seem easier to me
    finished_process = _krun(input_file=input_file, definition_dir=definition_dir, output=KRunOutput.KORE, depth=depth)
    # TODO: We can consider implementing a better error handling
    assert finished_process.returncode == 0, 'KRun failed'

    parsed = KoreParser(finished_process.stdout)
    return parsed.pattern()


def main(k_file: str, program: str, output_dir: str) -> None:
    print(f'Kompiling target {k_file} to {output_dir}')
    kompiled: Path = get_kompiled_dir(k_file, output_dir)
    get_kompiled_definition(kompiled)
    get_confguration_for_depth(kompiled, Path(program), 0)
    print('Done!')


if __name__ == '__main__':
    argparser = ArgumentParser()
    # First argument: path to the .K file
    argparser.add_argument('k_file', type=str)
    # Second argument: path to the program
    argparser.add_argument('program', type=str)
    # Path to the output directory
    argparser.add_argument('output_dir', type=str)
    args = argparser.parse_args()

    main(args.k_file, args.program, args.output_dir)
