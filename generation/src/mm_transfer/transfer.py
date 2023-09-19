from __future__ import annotations

import argparse
import os
from pathlib import Path

from mm_transfer.converter.converter import MetamathConverter
from mm_transfer.metamath.parser import load_database
from proof_generation.proof import ExecutionPhase, PrettyPrintingInterpreter


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument('input', help='Input Metamath database path')
    parser.add_argument('output', help='Output directory')
    parser.add_argument('filename', help='Output file name')
    parser.add_argument('--clean', default=True, help='Clean up the output directory if it exists')
    args = parser.parse_args()

    print('Parsing database...', end='', flush=True)
    input_database = load_database(args.input, include_proof=True)
    print(' Done.')

    # Prepare output dir
    output_dir = Path(args.output)
    if output_dir.exists():
        if args.clean:
            for file in output_dir.glob('*.mm'):
                file.unlink()
        else:
            print('Output directory already exists. Use --clean to overwrite.')
            return
    else:
        print('Creating output directory...')
        output_dir.mkdir()

    # Prepare the converter
    converter = MetamathConverter(input_database)
    assert converter

    print('Converting statements...', end='', flush=True)
    # TODO: Print files for different phases (gamma, claims, proofs)
    with open(os.path.join(output_dir, args.filename), 'w') as out:
        printer = PrettyPrintingInterpreter(phase=ExecutionPhase.Gamma, out=out)
        converter.interpret_axioms(printer)
    print(' Done.')


if __name__ == '__main__':
    main()
