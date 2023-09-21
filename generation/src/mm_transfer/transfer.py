from __future__ import annotations

import argparse
from pathlib import Path

import proof_generation.pattern as nf
import proof_generation.proof as p
from mm_transfer.converter.converter import MetamathConverter
from mm_transfer.metamath.parser import load_database


def exec_proof(converter: MetamathConverter, target: str, proofexp: p.ProofExp) -> None:
    assert isinstance(proofexp.interpreter, p.StatefulInterpreter)

    # We do not support ambiguities right now
    exported_proof = converter._lemmas[target][0].proof

    for lemma in exported_proof.applied_lemmas:
        lemma_label = exported_proof.labels[lemma]

        if lemma_label in converter.pattern_constructors:
            # Cannot call .pattern here, as I have what I need on stack
            if lemma_label == 'imp-is-pattern':
                assert isinstance(proofexp.interpreter.stack[-2], nf.Pattern)
                assert isinstance(proofexp.interpreter.stack[-1], nf.Pattern)
                proofexp.interpreter.implies(proofexp.interpreter.stack[-2], proofexp.interpreter.stack[-1])
        # TODO: phi0-is-pattern should be in pattern constructors
        elif lemma_label == 'ph0-is-pattern':
            proofexp.interpreter.metavar(0)
        elif lemma_label in converter.exported_axioms:
            proofexp.load_axiom(converter.get_axiom_by_name(lemma_label).pattern)
            # TODO: Instantiate
        elif lemma_label in converter.proof_rules:
            if lemma_label == 'proof-rule-prop-1':
                prop1 = proofexp.interpreter.prop1()
                assert isinstance(proofexp.interpreter.stack[-3], nf.Pattern)
                assert isinstance(proofexp.interpreter.stack[-2], nf.Pattern)
                proofexp.interpreter.instantiate(
                    prop1,
                    {0: proofexp.interpreter.stack[-3], 1: proofexp.interpreter.stack[-2]},
                )
            if lemma_label == 'proof-rule-prop-2':
                prop2 = proofexp.interpreter.prop2()
                assert isinstance(proofexp.interpreter.stack[-4], nf.Pattern)
                assert isinstance(proofexp.interpreter.stack[-3], nf.Pattern)
                assert isinstance(proofexp.interpreter.stack[-2], nf.Pattern)
                proofexp.interpreter.instantiate(
                    prop2,
                    {
                        0: proofexp.interpreter.stack[-4],
                        1: proofexp.interpreter.stack[-3],
                        2: proofexp.interpreter.stack[-2],
                    },
                )
            if lemma_label == 'proof-rule-mp':
                assert isinstance(proofexp.interpreter.stack[-2], p.Proved)
                assert isinstance(proofexp.interpreter.stack[-1], p.Proved)
                proofexp.interpreter.modus_ponens(proofexp.interpreter.stack[-2], proofexp.interpreter.stack[-1])

                conclusion_name, conclusion = (str(proofexp.interpreter.stack[-1]), proofexp.interpreter.stack[-1])
                proofexp.interpreter.save(conclusion_name, conclusion)
                proofexp.interpreter.pop(proofexp.interpreter.stack[-1])
                proofexp.interpreter.pop(proofexp.interpreter.stack[-1])
                proofexp.interpreter.pop(proofexp.interpreter.stack[-1])
                proofexp.interpreter.load(conclusion_name, conclusion)

    assert isinstance(proofexp.interpreter.stack[-1], p.Proved)
    proofexp.interpreter.publish_proof(proofexp.interpreter.stack[-1])


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument('input', help='Input Metamath database path')
    parser.add_argument('output', help='Output directory')
    parser.add_argument('target', help='Lemma whose proof is to be translated')
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

    class TranslatedProofSkeleton(p.ProofExp):
        @staticmethod
        def axioms() -> list[p.Pattern]:
            return extracted_axioms

        @staticmethod
        def claims() -> list[p.Pattern]:
            return extracted_claims

    # Export axioms and claims
    TranslatedProofSkeleton.main(['', 'binary', 'gamma', str(output_dir / f'{args.output}.ml-gamma')])
    TranslatedProofSkeleton.main(['', 'binary', 'claim', str(output_dir / f'{args.output}.ml-claim')])

    # Export proof
    with open(output_dir / f'{args.output}.ml-proof', 'wb') as out:
        proofexp = TranslatedProofSkeleton(
            p.SerializingInterpreter(
                p.ExecutionPhase.Proof, out, [p.Claim(claim) for claim in extracted_claims], extracted_axioms
            )
        )
        exec_proof(converter, args.target, proofexp)


if __name__ == '__main__':
    main()
