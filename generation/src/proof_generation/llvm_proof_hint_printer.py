from __future__ import annotations

from argparse import ArgumentParser

# import sys
from typing import TYPE_CHECKING

import pyk.kllvm.load  # noqa: F401
import pyk.kore.syntax as kore

from proof_generation.k.proof_gen import get_kompiled_definition, get_kompiled_dir, read_proof_hint
from proof_generation.llvm_proof_hint import LLVMFunctionEvent, LLVMHookEvent, LLVMRewriteEvent, LLVMRuleEvent

if TYPE_CHECKING:
    from proof_generation.llvm_proof_hint import Argument, LLVMRewriteTrace


def get_all_axioms(definition: kore.Definition) -> list[kore.Axiom]:
    axioms = []
    for module in definition.modules:
        for axiom in module.axioms:
            axioms.append(axiom)
    return axioms


def get_axiom_label(attrs: tuple[kore.App, ...]) -> str:
    for attr in attrs:
        if attr.symbol == 'label' and isinstance(attr.args[0], kore.String):
            return attr.args[0].value
    return ''


def get_axiom_location(attrs: tuple[kore.App, ...]) -> str:
    for attr in attrs:
        if attr.symbol == "org'Stop'kframework'Stop'attributes'Stop'Location" and isinstance(attr.args[0], kore.String):
            loc_slices = attr.args[0].value.split(',')
            start_row = loc_slices[0].split('(')[1]
            start_col = loc_slices[1]
            return start_row + ',' + start_col
    return ''


def axiom_gist_text(axiom: kore.Axiom) -> str:
    text = axiom.text.split("[UNIQUE'")[0]
    assert text, f'Error! Unexpected serialization of axiom: {axiom.text}'
    return text


def term_to_str(term: kore.Pattern, show_terms: int) -> str:
    if show_terms == 0:
        return '[kore]'
    elif show_terms == 1:
        assert isinstance(term, kore.App), f'Unexpected pattern: {term}'
        return f'[kore({term.symbol})'
    else:
        return term.text


class LLVMHintsPrinter:
    def __init__(self, hints: LLVMRewriteTrace, definition: kore.Definition) -> None:
        self.hints = hints
        self.axioms = get_all_axioms(definition)

    def print_trace(
        self,
        show_terms: int = 0,
        show_rules: bool = False,
    ) -> None:
        def dump(text: str, depth: int, end: str = '\n') -> None:
            print(f'{"  " * depth}{text}', end=end)

        def dump_rule(event: LLVMRewriteEvent, depth: int, show_terms: int) -> None:
            tag = 'Rule' if isinstance(event, LLVMRuleEvent) else 'Side Condition'
            idx = event.rule_ordinal
            axiom = self.axioms[idx]
            dump(
                f'{tag} {idx} [label: {get_axiom_label(axiom.attrs)}] [loc: {get_axiom_location(axiom.attrs)}] [substs: {len(event.substitution)}]',
                depth,
            )
            dump(f'{axiom_gist_text(axiom)}', depth + 1) if show_rules else None
            for v, t in event.substitution:
                dump(f'{v} = {term_to_str(t, show_terms)}', depth + 1)

        def dump_event(event: Argument, depth: int, show_terms: int, top: bool = False) -> None:
            if isinstance(event, LLVMRewriteEvent):
                dump_rule(event, depth, show_terms)
            elif isinstance(event, LLVMFunctionEvent):
                dump(f'Function: {event.name} @ {event.relative_position}', depth)
                for arg in event.args:
                    dump_event(arg, depth + 1, show_terms)
            elif isinstance(event, LLVMHookEvent):
                dump(f'Hook: {event.name} @ {event.relative_position}', depth)
                for arg in event.args:
                    dump_event(arg, depth + 1, show_terms)
                dump(f'Result: {term_to_str(event.result, show_terms)}', depth + 1)
            else:
                assert isinstance(event, kore.Pattern)
                dump(f'{"Config" if top else "Term"}: {term_to_str(event, show_terms)}', depth)

        depth = 0
        for step_event in self.hints.pre_trace:
            dump_event(step_event, depth, show_terms, top=True)
        dump(f'Init config: {term_to_str(self.hints.initial_config, show_terms)}', depth)
        for event in self.hints.trace:
            dump_event(event, depth, show_terms, top=True)


if __name__ == '__main__':
    argparser = ArgumentParser(
        prog='LLVM Hints Printer',
        description='Pretty-print the structure of an LLVM hints trace',
    )
    argparser.add_argument('hints', type=str, help='Path to the binary hints file')
    argparser.add_argument('kompiled_dir', type=str, help='Path to the kompiled directory of the language')
    argparser.add_argument(
        '--show_terms',
        type=int,
        default=0,
        help='Print out kore terms in full',
    )
    argparser.add_argument(
        '--show_rules',
        action='store_true',
        default=False,
        help='Print out the rewrite rule axioms in full',
    )

    args = argparser.parse_args()

    hints = read_proof_hint(args.hints)
    definition = get_kompiled_definition(get_kompiled_dir(args.kompiled_dir))

    printer = LLVMHintsPrinter(hints, definition)
    printer.print_trace(show_terms=args.show_terms, show_rules=args.show_rules)