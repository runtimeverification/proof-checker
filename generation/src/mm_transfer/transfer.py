from __future__ import annotations

import argparse
from pathlib import Path

from mm_transfer.converter.converter import MetamathConverter
from mm_transfer.metamath.parser import load_database
import proof_generation.proof as p

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
    assert converter

    extracted_axioms = [converter.get_axiom_by_name(axiom_name).pattern for axiom_name in converter.exported_axioms]
    extracted_claims = [converter.get_lemma_by_name(lemma_name).pattern for lemma_name in converter.lemmas]

    class NewProof(p.ProofExp):
        @staticmethod
        def axioms() -> list[p.Pattern]:
            return extracted_axioms

        @staticmethod
        def claims() -> list[p.Pattern]:
            return extracted_claims

    # Export axioms and claims
    NewProof.main(["", "binary", "gamma", output_dir / f"{args.output}.ml-gamma"])
    NewProof.main(["", "binary", "claim", output_dir / f"{args.output}.ml-claim"])

    # Export proof
    with open(output_dir / f"{args.output}.ml-proof", 'wb') as out:
        newproof = NewProof(p.SerializingInterpreter(
                p.ExecutionPhase.Proof,
                out,
                [p.Claim(claim) for claim in extracted_claims],
                extracted_axioms
            )
        )
        converter.exec_instruction(converter._declared_proof, newproof)


if __name__ == '__main__':
    main()
