from __future__ import annotations

from collections.abc import Callable
from enum import Enum
from typing import NamedTuple

import pyk.kore.syntax as kore

import proof_generation.pattern as nf
import proof_generation.proof as proof
import proof_generation.proofs.kore_lemmas as kl

ProofMethod = Callable[[proof.ProofExp], proof.Proved]


class AxiomType(Enum):
    Unclassified = 0
    RewriteRule = 1
    FunctionalSymbol = 2


class ConvertedAxiom(NamedTuple):
    kind: AxiomType
    pattern: nf.Pattern


Axioms = dict[AxiomType, list[ConvertedAxiom]]


class KoreConverter:
    def __init__(self, kore_definition: kore.Definition) -> None:
        self._definition = kore_definition

        self._symbols: dict[str, nf.Symbol] = {}
        self._evars: dict[str, nf.EVar] = {}
        self._svars: dict[str, nf.SVar] = {}
        self._metavars: dict[str, nf.MetaVar] = {}
        self._notations: dict[str, type[nf.Notation]] = {}

        # TODO: Update it depending on the numbering schemes used in hints
        self._axioms_to_choose_from: list[kore.Axiom] = self._retrieve_axioms()
        self._axioms_cache: dict[kore.Axiom, ConvertedAxiom] = {}

    def convert_pattern(self, pattern: kore.Pattern) -> nf.Pattern:
        """Convert the given pattern to the pattern in the new format."""
        return self._convert_pattern(pattern)

    def retrieve_axiom_by_index(self, position: int) -> Axioms:
        """Retrieve the axiom at the given ordinal."""
        kore_axiom = self._axioms_to_choose_from[position]
        converted = self._convert_axiom(kore_axiom)
        related_axioms = self.collect_related_axioms(converted)
        return self._organize_axioms([converted] + related_axioms)

    def collect_related_axioms(self, axiom: ConvertedAxiom) -> list[ConvertedAxiom]:
        # TODO: It goes without an implementation for now
        return []

    def _organize_axioms(self, axioms: list[ConvertedAxiom]) -> Axioms:
        """Organize the axioms by their type."""
        organized_axioms: Axioms = {}
        for axiom in axioms:
            organized_axioms.setdefault(axiom.kind, [])
            if axiom not in organized_axioms[axiom.kind]:
                organized_axioms[axiom.kind].append(axiom)

        return organized_axioms

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

    def _retrieve_axioms(self) -> list[kore.Axiom]:
        """Collect and save all axioms from the definition in Kore without converting them. This list will
        be used to resolve ordinals from hints to real axioms."""
        axioms: list[kore.Axiom] = []
        for kore_module in self._definition.modules:
            for axiom in kore_module.axioms:
                axioms.append(axiom)
        return axioms

    def _convert_pattern(self, pattern: kore.Pattern) -> nf.Pattern:
        """Convert the given pattern to the pattern in the new format."""
        match pattern:
            case kore.Rewrites(sort, left, right):
                rewrite_sort_symbol: nf.Pattern = self._resolve_symbol(sort)
                left_rw_pattern = self._convert_pattern(left)
                right_rw_pattern = self._convert_pattern(right)

                return kl.KoreRewrites(rewrite_sort_symbol, left_rw_pattern, right_rw_pattern)
            case kore.And(sort, left, right):
                and_sort_symbol: nf.Pattern = self._resolve_symbol(sort)
                left_and_pattern: nf.Pattern = self._convert_pattern(left)
                right_and_pattern: nf.Pattern = self._convert_pattern(right)

                return kl.KoreAnd(and_sort_symbol, left_and_pattern, right_and_pattern)
            case kore.Or(sort, left, right):
                or_sort_symbol: nf.Pattern = self._resolve_symbol(sort)
                left_or_pattern: nf.Pattern = self._convert_pattern(left)
                right_or_pattern: nf.Pattern = self._convert_pattern(right)

                return kl.KoreOr(or_sort_symbol, left_or_pattern, right_or_pattern)
            case kore.App(symbol, sorts, args):

                def chain_patterns(patterns: list[nf.Pattern]) -> nf.Pattern:
                    if len(patterns) == 0:
                        return nf.Bot()
                    else:
                        next_one, *patterns_left = patterns
                        return nf.App(next_one, chain_patterns(patterns_left))

                app_symbol: nf.Pattern = self._resolve_symbol(symbol)
                args_patterns: list[nf.Pattern] = [self._convert_pattern(arg) for arg in args]
                sorts_patterns: list[nf.Pattern] = [self._resolve_symbol(sort) for sort in sorts]

                args_chain = chain_patterns([app_symbol] + args_patterns) if len(args_patterns) > 0 else app_symbol
                sorts_chain = chain_patterns(sorts_patterns)

                assert isinstance(args_chain, (nf.App, nf.Symbol))
                return kl.KoreApplies(sorts_chain, args_chain)
            case kore.EVar(name, _):
                # TODO: Revisit when we have sorting implemented!
                # return self._resolve_evar(pattern)
                return self._resolve_metavar(name)
            case kore.Top(sort):
                top_sort_symbol: nf.Pattern = self._resolve_symbol(sort)
                return kl.KoreTop(top_sort_symbol)
            case kore.DV(sort, value):
                dv_sort_symbol: nf.Pattern = self._resolve_symbol(sort)
                value_symbol: nf.Pattern = self._resolve_symbol(value.value)
                return kl.KoreDv(dv_sort_symbol, value_symbol)

        raise NotImplementedError(f'Pattern {pattern} is not supported')

    def _resolve_symbol(self, pattern: kore.Pattern | kore.Sort | str) -> nf.Symbol:
        """Resolve the symbol in the given pattern."""
        if isinstance(pattern, str):
            if pattern not in self._symbols:
                self._symbols[pattern] = nf.Symbol('kore_' + pattern)
            return self._symbols[pattern]
        elif isinstance(pattern, kore.Sort):
            if pattern.name not in self._symbols:
                self._symbols[pattern.name] = nf.Symbol('kore_sort_' + pattern.name)
            return self._symbols[pattern.name]
        else:
            raise NotImplementedError(f'Pattern {pattern} is not supported')

    def _resolve_notation(self, name: str, symbol: nf.Symbol, arguments: list[nf.Pattern]) -> nf.Pattern:
        """Resolve the notation or make up one."""
        if name in self._notations:
            return self._notations[name](*arguments)
        else:
            return nf.FakeNotation(symbol, tuple(arguments))

    def _resolve_evar(self, evar: kore.EVar) -> nf.EVar:
        """Resolve the evar in the given pattern."""
        if evar.name not in self._evars:
            self._evars[evar.name] = nf.EVar(name=len(self._evars))
        return self._evars[evar.name]

    def _resolve_metavar(self, name: str) -> nf.MetaVar:
        """Resolve the metavar in the given pattern."""
        if name not in self._metavars:
            self._metavars[name] = nf.MetaVar(name=len(self._metavars))
        return self._metavars[name]

    def _lookup_metavar(self, name: str) -> nf.MetaVar:
        assert name in self._metavars.keys(), f'Variable name {name} not found in meta vars dict!'
        return self._metavars[name]

    def convert_substitution(
        self,
        subst: tuple[tuple[str, kore.Pattern], ...],
    ) -> dict[int, nf.Pattern]:
        substitutions = {}
        for id, pattern in subst:
            name = self._lookup_metavar(id).name
            substitutions[name] = self.convert_pattern(pattern)
        return substitutions
