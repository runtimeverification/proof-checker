from __future__ import annotations

import argparse
from pathlib import Path

from mm_transfer.converter.converter import MetamathConverter
from mm_transfer.metamath.parser import load_database
from proof_generation.proof import ExecutionPhase, PrettyPrintingInterpreter


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument('input', help='Input Metamath database path')
    parser.add_argument('output', help='Output directory')
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

    # Add them to the new format
    with open(output_dir / 'metavariables.ml-proof', 'w') as out:
        printer = PrettyPrintingInterpreter(phase=ExecutionPhase.Proof, out=out)
        converter.put_vars_on_stack(printer)


if __name__ == '__main__':
    main()
