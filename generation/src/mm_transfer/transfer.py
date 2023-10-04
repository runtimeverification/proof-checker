from __future__ import annotations

import argparse
import os
from pathlib import Path

from mm_transfer.converter.converter import MetamathConverter
from mm_transfer.converter.representation import AxiomWithAntecedents
from mm_transfer.metamath.parser import load_database
from proof_generation.basic_interpreter import ExecutionPhase
from proof_generation.pattern import Implication, MetaVar, Pattern
from proof_generation.proof import ProofExp
from proof_generation.proved import Proved
from proof_generation.stateful_interpreter import StatefulInterpreter


def exec_proof(converter: MetamathConverter, target: str, proofexp: ProofExp) -> None:
    assert isinstance(proofexp.interpreter, StatefulInterpreter)
    interpreter = lambda: proofexp.interpreter
    stack = lambda: proofexp.interpreter.stack

    def get_delta(metavars: tuple[str, ...]) -> dict[int, Pattern]:
        delta: dict[int, Pattern] = {}

        nargs = len(metavars)
        i = 0
        for metavar_label in metavars:
            metavar = converter.resolve_metavar(metavar_label)
            pat = stack()[-(nargs + 1) + i]
            assert isinstance(pat, Pattern)
            delta[metavar.name] = pat
            i += 1

        return delta

    def do_mp() -> None:
        left = stack()[-2]
        right = stack()[-1]
        assert isinstance(left, Proved)
        assert isinstance(right, Proved)
        interpreter().modus_ponens(left, right)

    # We do not support ambiguities right now
    exported_proof = converter.get_lemma_by_name(target).proof

    # lemma |-> memory id in MM
    mm_memory: list[Pattern | Proved] = []
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
                assert isinstance(left, Pattern)
                assert isinstance(right, Pattern)
                interpreter().app(left, right)
                continue

            if lemma_label == 'imp-is-pattern':
                left = stack()[-2]
                right = stack()[-1]
                assert isinstance(left, Pattern)
                assert isinstance(right, Pattern)
                interpreter().implies(left, right)
                continue

            # Construct the axiom on stack
            pat_constructor_axiom = converter.get_axiom_by_name(lemma_label)
            interpreter().pattern(pat_constructor_axiom.pattern)

            # Instantiate it with instantiations given by MM (as MM does this implicitly)
            if len(pat_constructor_axiom.metavars) > 0:
                pat = stack()[-1]
                assert isinstance(pat, Pattern)
                interpreter().instantiate_notation(pat, get_delta(converter.get_metavars_in_order(lemma_label)))

        # Lemma is one of these `metavar-is-pattern` functions
        elif lemma_label in converter._fp_label_to_pattern and isinstance(
            converter.get_floating_pattern_by_name(lemma_label)[0], MetaVar
        ):
            # TODO: phi0-is-pattern should be in pattern constructors
            pat = converter.get_floating_pattern_by_name(lemma_label)[0]
            assert isinstance(pat, MetaVar)
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
                assert isinstance(pat, Proved)
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
                assert isinstance(phi0, Pattern)
                assert isinstance(phi1, Pattern)
                interpreter().instantiate(
                    prop1,
                    {0: phi0, 1: phi1},
                )
            if lemma_label == 'proof-rule-prop-2':
                prop2 = interpreter().prop2()
                phi0 = stack()[-4]
                phi1 = stack()[-3]
                phi2 = stack()[-2]
                assert isinstance(phi0, Pattern)
                assert isinstance(phi1, Pattern)
                assert isinstance(phi2, Pattern)
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
    assert isinstance(pat, Proved)
    assert pat == Proved(converter.get_lemma_by_name(target).pattern)
    interpreter().publish_proof(pat)


# TODO: This is unsound and should be replaced with a different handling
def convert_to_implication(antecedents: tuple[Pattern, ...], conclusion: Pattern) -> Pattern:
    (ant, *ants) = antecedents

    if ants:
        return Implication(ant, convert_to_implication(tuple(ants), conclusion))

    return Implication(ant, conclusion)


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

    class TranslatedProofSkeleton(ProofExp):
        @staticmethod
        def axioms() -> list[Pattern]:
            return extracted_axioms

        @staticmethod
        def claims() -> list[Pattern]:
            return extracted_claims

        def execute_proofs_phase(self) -> None:
            assert self.interpreter.phase == ExecutionPhase.Proof
            exec_proof(converter, args.target, self)

    module = os.path.splitext(os.path.basename(args.input))[0]

    TranslatedProofSkeleton.main(['', 'memo', 'gamma', str(output_dir / f'{module}.ml-gamma')])
    TranslatedProofSkeleton.main(['', 'memo', 'claim', str(output_dir / f'{module}.ml-claim')])
    TranslatedProofSkeleton.main(['', 'memo', 'proof', str(output_dir / f'{module}.ml-proof')])


if __name__ == '__main__':
    main()
