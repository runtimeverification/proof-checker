from __future__ import annotations

import argparse
import os
from pathlib import Path

import proof_generation.pattern as nf
import proof_generation.proof as p
from mm_transfer.converter.converter import MetamathConverter
from mm_transfer.converter.representation import AxiomWithAntecedents
from mm_transfer.metamath.parser import load_database


def exec_proof(converter: MetamathConverter, target: str, proofexp: p.ProofExp) -> None:
    assert isinstance(proofexp.interpreter, p.StatefulInterpreter)
    interpreter = lambda: proofexp.interpreter
    stack = lambda: proofexp.interpreter.stack

    def get_delta(metavars: tuple[str, ...]) -> dict[int, nf.Pattern]:
        delta: dict[int, nf.Pattern] = {}

        nargs = len(metavars)
        i = 0
        for metavar_label in metavars:
            metavar = converter.resolve_metavar(metavar_label)
            pat = stack()[-(nargs + 1) + i]
            assert isinstance(pat, nf.Pattern)
            delta[metavar.name] = pat
            i += 1

        return delta

    def do_mp() -> None:
        left = stack()[-2]
        right = stack()[-1]
        assert isinstance(left, p.Proved)
        assert isinstance(right, p.Proved)
        interpreter().modus_ponens(left, right)

    # We do not support ambiguities right now
    exported_proof = converter.get_lemma_by_name(target).proof

    # lemma |-> memory id in MM
    mm_memory: list[nf.Pattern | p.Proved] = []
    # MM encoding offset
    memory_offset = len(exported_proof.labels)  # TODO: Add EH later

    # Keep track of proof step number
    for lemma in exported_proof.applied_lemmas:
        if lemma not in exported_proof.labels:
            if lemma == 0:
                # Z save
                pat = stack()[-1]
                mm_memory.append(pat)
                interpreter().save(str(pat), pat)
            else:
                # We play with memory, so we need to look for the original index in MM memory
                interpreter().load(str(mm_memory[lemma - memory_offset - 1]), mm_memory[lemma - memory_offset - 1])
            # We do not do anything else, as this was a load/save
            continue

        lemma_label = exported_proof.labels[lemma]

        # Lemma is one of these pattern constructors/notations
        if lemma_label in converter.pattern_constructors:
            # Cannot call .pattern here, as I have what I need on stack
            if lemma_label == 'app-is-pattern':
                left = stack()[-2]
                right = stack()[-1]
                assert isinstance(left, nf.Pattern)
                assert isinstance(right, nf.Pattern)
                interpreter().app(left, right)
                continue

            if lemma_label == 'imp-is-pattern':
                left = stack()[-2]
                right = stack()[-1]
                assert isinstance(left, nf.Pattern)
                assert isinstance(right, nf.Pattern)
                interpreter().implies(left, right)
                continue

            # Construct the axiom on stack
            pat_constructor_axiom = converter.get_axiom_by_name(lemma_label)
            interpreter().pattern(pat_constructor_axiom.pattern)

            # Instantiate it with instantiations given by MM (as MM does this implicitly)
            if len(pat_constructor_axiom.metavars) > 0:
                pat = stack()[-1]
                assert isinstance(pat, nf.Pattern)
                interpreter().instantiate_notation(pat, get_delta(converter.get_metavars_in_order(lemma_label)))

        # Lemma is one of these `metavar-is-pattern` functions
        elif lemma_label in converter._fp_label_to_pattern and isinstance(
            converter.get_floating_pattern_by_name(lemma_label)[0], nf.MetaVar
        ):
            # TODO: phi0-is-pattern should be in pattern constructors
            pat = converter.get_floating_pattern_by_name(lemma_label)[0]
            assert isinstance(pat, nf.MetaVar)
            interpreter().metavar(pat.name)

        # Lemma is in Gamma
        elif lemma_label in converter.exported_axioms:
            axiom = converter.get_axiom_by_name(lemma_label)
            saved_antecedents = []

            # For now, we treat EH's as antecedents in the pattern
            if isinstance(axiom, AxiomWithAntecedents):
                # This means the concrete antecedents are on stack given by MM stack
                # AFTER the instantiations for our lemma (as floatings go first)
                # We need to pop the antecedents to instantiate our axiom first
                for _ in axiom.antecedents:
                    saved_antecedents.append((str(stack()[-1]), stack()[-1]))
                    interpreter().save(str(stack()[-1]), stack()[-1])
                    interpreter().pop(stack()[-1])
                proofexp.load_axiom(convert_to_implication(axiom.antecedents, axiom.pattern))
            else:
                proofexp.load_axiom(axiom.pattern)

            # We need to instantiate the axiom depending on what we are given on stack
            if len(axiom.metavars) > 0:
                pat = stack()[-1]
                assert isinstance(pat, p.Proved)
                interpreter().instantiate(pat, get_delta(converter.get_metavars_in_order(lemma_label)))

            # Now we need to get rid of the antecedents
            if isinstance(axiom, AxiomWithAntecedents):
                for eh, pat in reversed(saved_antecedents):
                    interpreter().load(eh, pat)  # stack[-1]: eh1
                    pass  # stack[-2]: eh1 -> (eh2 -> (...))
                    do_mp()  # stack[-1]: eh2 -> (...)

        # Lemma is one of the fixed proof rules in the ML proof system
        elif lemma_label in converter.proof_rules:
            if lemma_label == 'proof-rule-prop-1':
                prop1 = interpreter().prop1()
                phi0 = stack()[-3]
                phi1 = stack()[-2]
                assert isinstance(phi0, nf.Pattern)
                assert isinstance(phi1, nf.Pattern)
                interpreter().instantiate(
                    prop1,
                    {0: phi0, 1: phi1},
                )
            if lemma_label == 'proof-rule-prop-2':
                prop2 = interpreter().prop2()
                phi0 = stack()[-4]
                phi1 = stack()[-3]
                phi2 = stack()[-2]
                assert isinstance(phi0, nf.Pattern)
                assert isinstance(phi1, nf.Pattern)
                assert isinstance(phi2, nf.Pattern)
                interpreter().instantiate(
                    prop2,
                    {
                        0: phi0,
                        1: phi1,
                        2: phi2,
                    },
                )
            if lemma_label == 'proof-rule-mp':
                do_mp()

                # We need to clean up redundant wellformedness checks
                conclusion_name, conclusion = (str(stack()[-1]), stack()[-1])
                interpreter().save(conclusion_name, conclusion)
                interpreter().pop(stack()[-1])
                interpreter().pop(stack()[-1])
                interpreter().pop(stack()[-1])
                interpreter().load(conclusion_name, conclusion)
        else:
            raise NotImplementedError(f'The proof label {lemma_label} is not recognized as an implemented instruction')

    pat = stack()[-1]
    assert isinstance(pat, p.Proved)
    assert pat == p.Proved(interpreter(), converter.get_lemma_by_name(target).pattern)
    interpreter().publish_proof(pat)


# TODO: This is unsound and should be replaced with a different handling
def convert_to_implication(antecedents: tuple[nf.Pattern, ...], conclusion: nf.Pattern) -> nf.Pattern:
    (ant, *ants) = antecedents

    if ants:
        return nf.Implication(ant, convert_to_implication(tuple(ants), conclusion))

    return nf.Implication(ant, conclusion)


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

    module = os.path.splitext(os.path.basename(args.input))[0]

    # Export axioms
    # Dry run
    claims = list(map(p.Claim, TranslatedProofSkeleton.claims()))
    counting_interpreter = p.CountingInterpreter(phase=p.ExecutionPhase.Gamma, claims=claims)
    proof_exp = TranslatedProofSkeleton(counting_interpreter)
    for axiom in TranslatedProofSkeleton.axioms():
        proof_exp.publish_axiom(proof_exp.interpreter.pattern(axiom))
    counting_interpreter.finalize()

    # Actual export
    with open(output_dir / f'{module}.ml-gamma', 'wb') as out:
        proof_exp = TranslatedProofSkeleton(p.MemoizingInterpreter(phase=p.ExecutionPhase.Gamma, claims=claims, out=out, counting_interpreter=counting_interpreter))
        for axiom in TranslatedProofSkeleton.axioms():
            proof_exp.publish_axiom(proof_exp.interpreter.pattern(axiom))

    # Export claims
    # Dry run
    claims = list(map(p.Claim, TranslatedProofSkeleton.claims()))
    counting_interpreter = p.CountingInterpreter(phase=p.ExecutionPhase.Claim, claims=claims)
    proof_exp = TranslatedProofSkeleton(counting_interpreter)
    for claim_expr in reversed(TranslatedProofSkeleton.claims()):
        proof_exp.publish_claim(proof_exp.interpreter.pattern(claim_expr))
    counting_interpreter.finalize()

    # Actual export
    with open(output_dir / f'{module}.ml-claim', 'wb') as out:
        proof_exp = TranslatedProofSkeleton(p.MemoizingInterpreter(phase=p.ExecutionPhase.Claim, claims=claims, out=out, counting_interpreter=counting_interpreter))
        for claim_expr in reversed(TranslatedProofSkeleton.claims()):
            proof_exp.publish_claim(proof_exp.interpreter.pattern(claim_expr))

    # Export proof dry run
    counting_interpreter = p.CountingInterpreter(phase=p.ExecutionPhase.Proof, claims=[p.Claim(claim) for claim in extracted_claims], axioms=extracted_axioms)
    proofexp = TranslatedProofSkeleton(counting_interpreter)
    exec_proof(converter, args.target, proofexp)
    counting_interpreter.finalize()

    # Export proof
    with open(output_dir / f'{module}.ml-proof', 'wb') as out:
        proofexp = TranslatedProofSkeleton(
            p.MemoizingInterpreter(
                phase=p.ExecutionPhase.Proof, out=out, claims=[p.Claim(claim) for claim in extracted_claims], axioms=extracted_axioms, counting_interpreter=counting_interpreter
            )
        )
        exec_proof(converter, args.target, proofexp)


if __name__ == '__main__':
    main()
