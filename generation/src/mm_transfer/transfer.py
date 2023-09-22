from __future__ import annotations

import argparse
from pathlib import Path

import proof_generation.pattern as nf
import proof_generation.proof as p
from mm_transfer.converter.converter import MetamathConverter
from mm_transfer.metamath.parser import load_database
from mm_transfer.converter.representation import AxiomWithAntecedents


def exec_proof(converter: MetamathConverter, target: str, proofexp: p.ProofExp) -> None:
    assert isinstance(proofexp.interpreter, p.StatefulInterpreter)
    interpreter = lambda: proofexp.interpreter
    stack = lambda: proofexp.interpreter.stack

    def get_delta(metavars: tuple[str, ...], essential_hypotheses: int) -> dict[int, nf.Pattern]:
        delta: dict[int, nf.Pattern] = {}

        nargs = len(metavars) + essential_hypotheses

        i = 0
        for metavar_label in metavars:
            metavar = converter.resolve_metavar(metavar_label)
            delta[metavar.name] = stack()[-(nargs + 1) + i]
            i += 1

        return delta

    fps = list(map(lambda var_id: var_id + "-is-pattern", converter._floating_patterns))

    # We do not support ambiguities right now
    exported_proof = converter._lemmas[target][0].proof

    for (_step, lemma) in enumerate(exported_proof.applied_lemmas):
        lemma_label = exported_proof.labels[lemma]

        if lemma_label in converter.pattern_constructors:
            # Cannot call .pattern here, as I have what I need on stack
            if lemma_label == 'app-is-pattern':
                assert isinstance(stack()[-2], nf.Pattern)
                assert isinstance(stack()[-1], nf.Pattern)
                interpreter().app(stack()[-2], stack()[-1])
                continue

            if lemma_label == 'imp-is-pattern':
                assert isinstance(stack()[-2], nf.Pattern)
                assert isinstance(stack()[-1], nf.Pattern)
                interpreter().implies(stack()[-2], stack()[-1])
                continue

            interpreter().pattern(converter._axioms[lemma_label][0].pattern)

            if len(converter._axioms[lemma_label][0].metavars) > 0:
                interpreter().instantiate_notation(
                    stack()[-1],
                    get_delta(converter.get_metavars_in_order(lemma_label), 0)
                )
        # TODO: phi0-is-pattern should be in pattern constructors
        elif lemma_label in fps:
            interpreter().metavar(fps.index(lemma_label))

        elif lemma_label in converter.exported_axioms:
            axiom = converter.get_axiom_by_name(lemma_label)
            proofexp.load_axiom(axiom.pattern)

            essential_hypotheses = 0

            if isinstance(axiom, AxiomWithAntecedents):
                essential_hypotheses = len(axiom.antecedents)

            # We need to instantiate the axiom depending on what we are given on stack
            if len(converter._axioms[lemma_label][0].metavars) > 0:
                interpreter().instantiate(
                    stack()[-1],
                    get_delta(converter.get_metavars_in_order(lemma_label), essential_hypotheses)
                )

            # If we have EH's, we need to apply the remaining arguments with MP
            if essential_hypotheses:
                pass
        elif lemma_label in converter.proof_rules:
            if lemma_label == 'proof-rule-prop-1':
                prop1 = interpreter().prop1()
                assert isinstance(stack()[-3], nf.Pattern)
                assert isinstance(stack()[-2], nf.Pattern)
                interpreter().instantiate(
                    prop1,
                    {0: stack()[-3], 1: stack()[-2]},
                )
            if lemma_label == 'proof-rule-prop-2':
                prop2 = interpreter().prop2()
                assert isinstance(stack()[-4], nf.Pattern)
                assert isinstance(stack()[-3], nf.Pattern)
                assert isinstance(stack()[-2], nf.Pattern)
                interpreter().instantiate(
                    prop2,
                    {
                        0: stack()[-4],
                        1: stack()[-3],
                        2: stack()[-2],
                    },
                )
            if lemma_label == 'proof-rule-mp':
                assert isinstance(stack()[-2], p.Proved)
                assert isinstance(stack()[-1], p.Proved)
                interpreter().modus_ponens(stack()[-2], stack()[-1])

                conclusion_name, conclusion = (str(stack()[-1]), stack()[-1])
                interpreter().save(conclusion_name, conclusion)
                interpreter().pop(stack()[-1])
                interpreter().pop(stack()[-1])
                interpreter().pop(stack()[-1])
                interpreter().load(conclusion_name, conclusion)

    assert isinstance(stack()[-1], p.Proved)
    interpreter().publish_proof(stack()[-1])


# TODO: This is unsound and should be replaced with a different handling
def convert_to_implication(antecedents: tuple[nf.Pattern], conclusion: nf.Pattern) -> nf.Pattern:
    antecedent, *antecedents = antecedents

    if antecedents:
        return nf.Implication(
            antecedent,
            convert_to_implication(
                antecedents, conclusion
            )
        )

    return nf.Implication(antecedent, conclusion)


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

    extracted_axioms = []
    for axiom_name in converter.exported_axioms:
        axiom = converter.get_axiom_by_name(axiom_name)
        if isinstance(axiom, AxiomWithAntecedents):
            extracted_axioms.append(convert_to_implication(axiom.antecedents, axiom.pattern))
            continue
        extracted_axioms.append(axiom.pattern)

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
