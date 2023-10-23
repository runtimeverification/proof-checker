from __future__ import annotations

from collections.abc import Callable
from enum import Enum
from typing import TYPE_CHECKING, NamedTuple

import pyk.kore.syntax as kore

import proof_generation.pattern as nf
import proof_generation.proof as proof
import proof_generation.proofs.kore_lemmas as kl
import proof_generation.proofs.propositional as prop

if TYPE_CHECKING:
    from kore_transfer.generate_hints import KoreHint

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

        # TODO: We don't need this attribute. We need to collect these axioms on demand when we need them
        self._symbol_axioms: dict[str, kore.Axiom] = {}

        # TODO: Update it depending on the numbering schemes used in hints
        self._axioms_to_choose_from: list[kore.Axiom] = self._retrieve_axioms()
        self._axioms_cache: dict[kore.Axiom, ConvertedAxiom] = {}

    def convert_pattern(self, pattern: kore.Pattern) -> nf.Pattern:
        """Convert the given pattern to the pattern in the new format."""
        return self._convert_pattern(pattern)

    def retrieve_axioms_for_hint(self, hint: KoreHint) -> Axioms:
        """Retrieve the axiom at the given ordinal."""
        kore_axiom = self._axioms_to_choose_from[hint.axiom_ordinal]
        converted = self._convert_axiom(kore_axiom)
        related_axioms = self.collect_axioms_for_substitutions(hint.substitutions)

        return self._organize_axioms([converted] + related_axioms)

    def collect_axioms_for_substitutions(self, substitutions: dict[str, nf.Pattern]) -> list[ConvertedAxiom]:
        added_axioms = []
        for name in substitutions.keys():
            # The line below is needed until we use metavars instead of EVars
            self._resolve_metavar(name)

            if name in self._symbol_axioms:
                # Look up for an axiom
                converted_pattern = self._convert_pattern(self._symbol_axioms[name].pattern)
            else:
                # Generate axiom if it is missing
                evar = self._resolve_evar(name)

                # TODO: We need an equality notation there
                # TODO: Should we use Kore or NF pattern here? I am using the NF because the sort is unclear
                converted_pattern = nf.Exists(0, prop.And(nf.Implies(nf.EVar(0), evar), nf.Implies(evar, nf.EVar(0))))

            added_axioms.append(ConvertedAxiom(AxiomType.FunctionalSymbol, converted_pattern))
        return added_axioms

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

        def if_functional(kore_axiom: kore.Axiom) -> bool:
            for attr in kore_axiom.attrs:
                if isinstance(attr, kore.App) and attr.symbol == 'functional':
                    return True
            return False

        axioms: list[kore.Axiom] = []
        for kore_module in self._definition.modules:
            for axiom in kore_module.axioms:
                # TODO: Do we need this filtering there?
                # Collect axioms that state existence of a EVar
                if (
                    if_functional(axiom)
                    and isinstance(axiom.pattern, kore.Exists)
                    and isinstance(axiom.pattern.pattern, kore.Equals)
                    and isinstance(axiom.pattern.pattern.right, kore.App)
                    and len(axiom.pattern.pattern.right.sorts) == 0
                    and len(axiom.pattern.pattern.right.args) == 0
                    and axiom.pattern.pattern.left == axiom.pattern.var
                ):
                    # self._symbol_axioms[var] = axiom
                    symbol = axiom.pattern.pattern.right.symbol
                    self._symbol_axioms[symbol] = axiom

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

    def _resolve_evar(self, name: str) -> nf.EVar:
        """Resolve the evar in the given pattern."""
        if name not in self._evars:
            self._evars[name] = nf.EVar(name=len(self._evars))
        return self._evars[name]

    def _resolve_metavar(self, name: str) -> nf.MetaVar:
        """Resolve the metavar in the given pattern."""
        if name not in self._metavars:
            self._metavars[name] = nf.MetaVar(name=len(self._metavars))
        return self._metavars[name]

    def _lookup_metavar(self, name: str) -> nf.MetaVar:
        assert name in self._metavars.keys(), f'Variable name {name} not found in meta vars dict!'
        return self._metavars[name]

    def convert_substitution(self, subst: dict[str, nf.Pattern]) -> dict[int, nf.Pattern]:
        # TODO: Remove this function eventually, it is needed until we use EVars instead of metavars
        substitutions = {}
        for id, pattern in subst.items():
            name = self._lookup_metavar(id).name
            substitutions[name] = pattern
        return substitutions
