from __future__ import annotations

from collections.abc import Callable
from enum import Enum
from typing import TYPE_CHECKING, NamedTuple

import pyk.kore.syntax as kore

import proof_generation.proof as proof
import proof_generation.proofs.kore_lemmas as kl
import proof_generation.proofs.propositional as prop
from kore_transfer.generate_hints import FunEvent, HookEvent
from proof_generation.pattern import App, EVar, Exists, Implies, MetaVar, NotationPlaceholder, Symbol

if TYPE_CHECKING:
    from kore_transfer.generate_hints import KoreHint
    from proof_generation.pattern import Notation, Pattern, SVar

ProofMethod = Callable[[proof.ProofExp], proof.Proved]


class AxiomType(Enum):
    Unclassified = 0
    RewriteRule = 1
    FunctionalSymbol = 2
    FunctionEvent = 3
    HookEvent = 4


class ConvertedAxiom(NamedTuple):
    kind: AxiomType
    pattern: Pattern


Axioms = dict[AxiomType, list[ConvertedAxiom]]


class KoreConverter:
    def __init__(self, kore_definition: kore.Definition) -> None:
        self._definition = kore_definition

        self._symbols: dict[str, Symbol] = {}
        self._evars: dict[str, EVar] = {}
        self._svars: dict[str, SVar] = {}
        self._metavars: dict[str, MetaVar] = {}
        self._notations: dict[str, type[Notation]] = {}

        # TODO: Update it depending on the numbering schemes used in hints
        self._axioms_to_choose_from: list[kore.Axiom] = self._retrieve_axioms()
        self._axioms_cache: dict[kore.Axiom, ConvertedAxiom] = {}

    def convert_pattern(self, pattern: kore.Pattern) -> Pattern:
        """Convert the given pattern to the pattern in the new format."""
        return self._convert_pattern(pattern)

    def collect_functional_axioms(self, hint: KoreHint) -> Axioms:
        added_axioms = self.construct_subst_axioms(hint)
        added_axioms.extend(self.construct_event_axioms(hint))
        return self._organize_axioms(added_axioms)

    def construct_subst_axioms(self, hint: KoreHint) -> list[ConvertedAxiom]:
        subst_axioms = []
        for pattern in hint.substitutions.values():
            # TODO: Requires equality to be implemented
            converted_pattern = Exists(0, prop.And(Implies(EVar(0), pattern), Implies(pattern, EVar(0))))
            subst_axioms.append(ConvertedAxiom(AxiomType.FunctionalSymbol, converted_pattern))
        return subst_axioms

    def construct_event_axioms(self, hint: KoreHint) -> list[ConvertedAxiom]:
        event_axioms = []
        for event in hint.functional_events:
            if isinstance(event, FunEvent):
                # TODO: construct the proper axiom using event.name, event.relative_position
                pattern = Implies(EVar(0), EVar(0))
                event_axioms.append(ConvertedAxiom(AxiomType.FunctionEvent, pattern))
            if isinstance(event, HookEvent):
                # TODO: construct the proper axiom using event.name, event.args, and event.result
                pattern = Implies(EVar(0), EVar(0))
                event_axioms.append(ConvertedAxiom(AxiomType.HookEvent, pattern))
        return event_axioms

    def retrieve_axiom_for_ordinal(self, ordinal: int) -> ConvertedAxiom:
        """Retrieve the axiom for the given ordinal."""
        assert ordinal < len(self._axioms_to_choose_from), f'Ordinal {ordinal} is out of range!'

        kore_axiom = self._axioms_to_choose_from[ordinal]
        return self._convert_axiom(kore_axiom)

    def convert_substitutions(self, subst: dict[str, kore.Pattern]) -> dict[int, Pattern]:
        substitutions = {}
        for id, kore_pattern in subst.items():
            # TODO: Replace it with the EVar later
            name = self._lookup_metavar(id).name
            substitutions[name] = self._convert_pattern(kore_pattern)
        return substitutions

    def _convert_axiom(self, kore_axiom: kore.Axiom) -> ConvertedAxiom:
        if kore_axiom in self._axioms_cache:
            return self._axioms_cache[kore_axiom]

        # Check the axiom type
        preprocessed_pattern: kore.Pattern
        if isinstance(kore_axiom.pattern, kore.Rewrites):
            axiom_type = AxiomType.RewriteRule

            pattern = kore_axiom.pattern
            assert isinstance(pattern, kore.Rewrites)
            assert isinstance(pattern.left, kore.And)
            assert isinstance(pattern.right, kore.And)

            # TODO: Remove side conditions for now
            preprocessed_pattern = kore.Rewrites(pattern.sort, pattern.left.left, pattern.right.left)
        else:
            axiom_type = AxiomType.Unclassified
            preprocessed_pattern = kore_axiom.pattern

        assert isinstance(preprocessed_pattern, kore.Pattern)
        converted_pattern = self._convert_pattern(preprocessed_pattern)
        converted_axiom = ConvertedAxiom(axiom_type, converted_pattern)
        self._axioms_cache[kore_axiom] = converted_axiom
        return converted_axiom

    def _organize_axioms(self, axioms: list[ConvertedAxiom]) -> Axioms:
        """Organize the axioms by their type."""
        organized_axioms: Axioms = {}
        for axiom in axioms:
            organized_axioms.setdefault(axiom.kind, [])
            if axiom not in organized_axioms[axiom.kind]:
                organized_axioms[axiom.kind].append(axiom)

        return organized_axioms

    def _retrieve_axioms(self) -> list[kore.Axiom]:
        """Collect and save all axioms from the definition in Kore without converting them. This list will
        be used to resolve ordinals from hints to real axioms."""
        axioms: list[kore.Axiom] = []
        for kore_module in self._definition.modules:
            for axiom in kore_module.axioms:
                axioms.append(axiom)
        return axioms

    def _convert_pattern(self, pattern: kore.Pattern) -> Pattern:
        """Convert the given pattern to the pattern in the new format."""
        match pattern:
            case kore.Rewrites(sort, left, right):
                rewrite_sort_symbol: Pattern = self._resolve_symbol(sort)
                left_rw_pattern = self._convert_pattern(left)
                right_rw_pattern = self._convert_pattern(right)

                return kl.KoreRewrites(rewrite_sort_symbol, left_rw_pattern, right_rw_pattern)
            case kore.And(sort, left, right):
                and_sort_symbol: Pattern = self._resolve_symbol(sort)
                left_and_pattern: Pattern = self._convert_pattern(left)
                right_and_pattern: Pattern = self._convert_pattern(right)

                return kl.KoreAnd(and_sort_symbol, left_and_pattern, right_and_pattern)
            case kore.Or(sort, left, right):
                or_sort_symbol: Pattern = self._resolve_symbol(sort)
                left_or_pattern: Pattern = self._convert_pattern(left)
                right_or_pattern: Pattern = self._convert_pattern(right)

                return kl.KoreOr(or_sort_symbol, left_or_pattern, right_or_pattern)
            case kore.App(symbol, sorts, args):

                def chain_patterns(patterns: list[Pattern]) -> Pattern:
                    *patterns_left, next_one = patterns
                    if len(patterns_left) == 0:
                        return next_one
                    else:
                        return App(chain_patterns(patterns_left), next_one)

                app_symbol: Pattern = self._resolve_symbol(symbol)
                args_patterns: list[Pattern] = [self._convert_pattern(arg) for arg in args]
                sorts_patterns: list[Pattern] = [self._resolve_symbol(sort) for sort in sorts]

                args_chain = chain_patterns([app_symbol] + args_patterns)

                application_sorts = sorts_patterns if sorts_patterns else [prop.Top()]
                assert isinstance(args_chain, (App, Symbol))
                return kl.KoreApplies(tuple(application_sorts), args_chain)
            case kore.EVar(name, _):
                # TODO: Revisit when we have sorting implemented!
                # return self._resolve_evar(pattern)
                return self._resolve_metavar(name)
            case kore.Top(sort):
                top_sort_symbol: Pattern = self._resolve_symbol(sort)
                return kl.KoreTop(top_sort_symbol)
            case kore.DV(sort, value):
                dv_sort_symbol: Pattern = self._resolve_symbol(sort)
                value_symbol: Pattern = self._resolve_symbol(value.value)
                return kl.KoreDv(dv_sort_symbol, value_symbol)

        raise NotImplementedError(f'Pattern {pattern} is not supported')

    def _resolve_symbol(self, pattern: kore.Pattern | kore.Sort | str) -> Symbol:
        """Resolve the symbol in the given pattern."""
        if isinstance(pattern, str):
            if pattern not in self._symbols:
                self._symbols[pattern] = Symbol('kore_' + pattern)
            return self._symbols[pattern]
        elif isinstance(pattern, kore.Sort):
            if pattern.name not in self._symbols:
                self._symbols[pattern.name] = Symbol('kore_sort_' + pattern.name)
            return self._symbols[pattern.name]
        else:
            raise NotImplementedError(f'Pattern {pattern} is not supported')

    def _resolve_notation(self, name: str, symbol: Symbol, arguments: list[Pattern]) -> Pattern:
        """Resolve the notation or make up one."""
        if name in self._notations:
            return self._notations[name](*arguments)
        else:
            return NotationPlaceholder(symbol, tuple(arguments))

    def _resolve_evar(self, name: str) -> EVar:
        """Resolve the evar in the given pattern."""
        if name not in self._evars:
            self._evars[name] = EVar(name=len(self._evars))
        return self._evars[name]

    def _resolve_metavar(self, name: str) -> MetaVar:
        """Resolve the metavar in the given pattern."""
        if name not in self._metavars:
            self._metavars[name] = MetaVar(name=len(self._metavars))
        return self._metavars[name]

    def _lookup_metavar(self, name: str) -> MetaVar:
        assert name in self._metavars.keys(), f'Variable name {name} not found in meta vars dict!'
        return self._metavars[name]
