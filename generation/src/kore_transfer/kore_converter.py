from __future__ import annotations

from collections.abc import Callable
from enum import Enum
from re import match
from typing import TYPE_CHECKING, NamedTuple
from dataclasses import dataclass, field

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


@dataclass(frozen=True)
class KSort:
    name: str
    hooked: bool = field(default=False)

    @property
    def aml_symbol(self) -> Symbol:
        return Symbol('ksort_' + self.name)


class KSortVar(KSort):
    pass


@dataclass(frozen=True)
class KSymbol:
    name: str
    input_sorts: tuple[KSort, ...]
    output_sort: KSort
    is_functional: bool
    is_ctor: bool
    is_cell: bool

    @property
    def aml_symbol(self) -> Symbol:
        return Symbol('kore_' + self.name)

    @property
    def aml_notation(self) -> Notation:
        raise NotImplementedError()


@dataclass(frozen=True)
class KRewritingRule:
    ordinal: int
    pattern: kl.KoreRewrites


@dataclass(frozen=True)
class KEquationalRule:
    ordinal: int
    pattern: Pattern


class Converter:

    def __init__(self) -> None:
        self._parsing = False

    def __enter__(self) -> Converter:
        """It is not allows to change the semantics except while parsing."""
        self._parsing = True
        return self

    def __exit__(self, exc_type, exc_value, traceback) -> None:
        """It is not allows to change the semantics except while parsing."""
        self._parsing = False


def converting_method(func):
    """Helps to forbid calling methods that change the semantics outside of parsing."""
    def wrapper(self, *args, **kwargs):
        assert isinstance(self, Converter)
        if self._parsing:
            return func(self, *args, **kwargs)
        else:
            raise ValueError('Cannot call parsing method on immutable theory')
    return wrapper


class KModue(Converter):

    def __init__(self, name: str) -> None:
        self._name = name
        # Ordinal -> axiom
        self._imported_modules: tuple[KModue, ...] = ()
        self._sorts: dict[str, KSort] = {}
        self._symbols: dict[str, KSymbol] = {}
        self._axioms: dict[int, KRewritingRule | KEquationalRule] = {}

    def __enter__(self) -> KModue:
        """It is not allows to change the semantics except while parsing."""
        obj = super().__enter__()
        assert isinstance(obj, KModue)
        return obj

    @property
    def name(self) -> str:
        return self._name

    def has_ordinal(self, ordinal) -> bool:
        return True if ordinal >= min(self._axioms.keys()) and ordinal <= max(self._axioms.keys()) else False

    @converting_method
    def import_module(self, module: KModue) -> None:
        if module in self._imported_modules:
            raise ValueError(f'Sort {module.name} already exists!')
        self._imported_modules += (module,)

    @converting_method
    def sort(self, name) -> KSort:
        return self._sort(name, False)

    @converting_method
    def hooked_sort(self, name) -> KSort:
        return self._sort(name, True)

    def _sort(self, name, hooked) -> KSort:
        if name in self._sorts:
            raise ValueError(f'Sort {name} has been already added!')
        self._sorts[name] = KSort(name, hooked)
        return self._sorts[name]

    @converting_method
    def symbol(self, name, input_sorts: tuple[KSort | KSortVar, ...], output_sort: KSort | KSortVar, is_functional: bool, is_ctor: bool, is_cell: bool) -> KSymbol:
        if name in self._symbols:
            raise ValueError(f'Symbol {name} has been already added!')
        symbol = KSymbol(name, input_sorts, output_sort, is_functional, is_ctor, is_cell)
        self._symbols[name] = symbol
        return symbol

    @converting_method
    def equational_rewrite(self, pattern) -> KEquationalRule:
        # TODO: Add the ordinal, save to the collection
        return KEquationalRule(0, pattern)

    @converting_method
    def rewrite_rule(self, pattern: kl.KoreRewrites) -> KRewritingRule:
        # TODO: Add the ordinal, save to the collection
        return KRewritingRule(0, pattern)

    def get_sort(self, name: str) -> KSort:
        if name in self._sorts:
            return self._sorts[name]

        for module in self._imported_modules:
            try:
                sort = module.get_sort(name)
                return sort
            except ValueError:
                continue
        raise ValueError(f'Sort {name} not found in the module {self.name}')

    def get_symbol(self, name: str) -> KSymbol:
        if name in self._symbols:
            return self._symbols[name]

        for module in self._imported_modules:
            try:
                symbol = module.get_symbol(name)
                return symbol
            except ValueError:
                continue
        raise ValueError(f'Symbol {name} not found in the module {self.name}')


class LanguageSemantics(Converter):
    GENERATED_TOP_SYMBOL = "Lbl'-LT-'generatedTop'-GT-'"

    def __init__(self, kore_definition: kore.Definition | None) -> None:
        self._imported_modules: tuple[KModue, ...] = ()

        # TODO: Obsolete
        self._definition = kore_definition
        self._evars: dict[str, EVar] = {}
        self._svars: dict[str, SVar] = {}
        self._metavars: dict[str, MetaVar] = {}        

        # Kore object cache
        self._notations: dict[str, Notation] = {}
        self._axioms_cache: dict[kore.Axiom, ConvertedAxiom] = {}
        self._functional_symbols: set[Symbol] = set()
        self._cell_symbols: set[str] = {self.GENERATED_TOP_SYMBOL}
        if kore_definition:
            self._axioms_to_choose_from: list[kore.Axiom] = self._retrieve_axioms()
            self._raw_functional_symbols: set[str] = self._collect_functional_symbols()

    @property
    def modules(self) -> tuple[KModue, ...]:
        return self._imported_modules

    def __enter__(self) -> LanguageSemantics:
        """It is not allows to change the semantics except while parsing."""
        obj = super().__enter__()
        assert isinstance(obj, LanguageSemantics)
        return obj

    @staticmethod
    def from_kore_definition(kore_definition: kore.Definition) -> LanguageSemantics:
        """Create a new instance of LanguageSemantics from the given Kore definition."""
        with LanguageSemantics(kore_definition) as semantics:
            for kore_module in kore_definition.modules:
                with semantics.module(kore_module.name) as module:
                    for sentence in kore_module.sentences:
                        if isinstance(sentence, kore.Import):
                            # Add imports
                            module.import_module(semantics.get_module(sentence.module_name))
                        elif isinstance(sentence, kore.SortDecl):
                            # Add sorts
                            if hasattr(sentence, 'hooked') and sentence.hooked:
                                module.hooked_sort(sentence.name)
                            else:
                                module.sort(sentence.name)
                        elif isinstance(sentence, kore.SymbolDecl):
                            symbol = sentence.symbol.name
                            param_sorts: list[KSort | KSortVar] = []
                            for param_sort in sentence.param_sorts:
                                match param_sort:
                                    case kore.SortVar(name):
                                        param_sorts.append(KSortVar(name))
                                    case kore.SortApp(name):
                                        param_sorts.append(module.get_sort(name))
                                    case _:
                                        raise NotImplementedError(f'Sort {param_sort} is not supported')                            
                            if isinstance(sentence.sort, kore.SortVar):
                                mapping = {s.name: s for s in param_sorts}
                                # TODO: This is a bit unexpected but despite the actual syntax like:
                                #  symbol inj{From, To}(From) : To [sortInjection{}()]
                                # The sort parameter list doesn't contain the last parameter To. So we saving it back
                                # assert sentence.sort.name in mapping
                                if sentence.sort.name not in mapping:
                                    sort = KSortVar(sentence.sort.name)
                                    param_sorts.append(sort)
                                else:
                                    sort = mapping[sentence.sort.name]
                            else:
                                sort = module.get_sort(sentence.sort.name)
                            attrs = [attr.symbol for attr in sentence.attrs if isinstance(attr, kore.App)]

                            # TODO: Support cells
                            module.symbol(symbol, tuple(param_sorts), sort, 'functional' in attrs, 'constructor' in attrs, False)
                        elif isinstance(sentence, kore.Axiom):
                            # Add axioms
                            if isinstance(sentence.pattern, kore.Rewrites):
                                pattern = sentence.pattern
                                assert isinstance(pattern, kore.Rewrites)
                                assert isinstance(pattern.left, kore.And)
                                assert isinstance(pattern.right, kore.And)

                                # TODO: Remove side conditions for now
                                preprocessed_pattern = kore.Rewrites(pattern.sort, pattern.left.left, pattern.right.left)
                                parsed_pattern = semantics._convert_pattern(preprocessed_pattern)
                                assert isinstance(parsed_pattern, kl.KoreRewrites)
                                module.rewrite_rule(parsed_pattern)
                            # TODO: Cannot parse everything yet
                            # elif isinstance(sentence.pattern, kore.Equals):
                            #     parsed_pattern = semantics._convert_pattern(sentence.pattern)
                            #     module.equational_rewrite(parsed_pattern)

            return semantics

    @property
    def main_module(self):
        # TODO: This is a heuristic
        return self._imported_modules[-1]

    @converting_method
    def module(self, name: str) -> KModue:
        module = KModue(name)
        self._imported_modules += (module,)
        return module

    def get_module(self, name: str) -> KModue:
        for module in self._imported_modules:
            if module.name == name:
                return module
        raise ValueError(f'Module {name} not found')

    def get_sort(self, name: str) -> KSort:
        return self.main_module.get_sort(name)

    def get_symbol(self, name: str) -> KSymbol:
        return self.main_module.get_symbol(name)

    def convert_pattern(self, pattern: kore.Pattern) -> Pattern:
        """Convert the given pattern to the pattern in the new format."""
        return self._convert_pattern(pattern)

    # TODO: Methods added before the refactoring:
    def collect_functional_axioms(self, hint: KoreHint) -> Axioms:
        added_axioms = self._construct_subst_axioms(hint)
        added_axioms.extend(self._construct_event_axioms(hint))
        return self._organize_axioms(added_axioms)

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

    def _collect_functional_symbols(self) -> set[str]:
        """Collect all functional symbols from the definition."""
        functional_symbols: set[str] = set()
        for kore_module in self._definition.modules:
            for symbol_declaration in kore_module.symbol_decls:
                if any(attr.symbol == 'functional' for attr in symbol_declaration.attrs if isinstance(attr, kore.App)):
                    functional_symbols.add(symbol_declaration.symbol.name)
        return functional_symbols

    def _construct_subst_axioms(self, hint: KoreHint) -> list[ConvertedAxiom]:
        subst_axioms = []
        # TODO: Refactoring pending ...
        # for pattern in hint.substitutions.values():
        #     # Doublecheck that the pattern is a functional symbol and it is valid to generate the axiom
        #     assert isinstance(
        #         pattern, kl.KoreApplies | kl.Cell
        #     ), f'Expected application of a Kore symbol, got {str(pattern)}'
        #     if isinstance(pattern.phi0, App) and isinstance(pattern.phi0.left, Symbol):
        #         assert pattern.phi0.left in self._functional_symbols
        #     elif isinstance(pattern.phi0, Symbol | kl.Cell):
        #         assert pattern.phi0 in self._functional_symbols
        #     else:
        #         raise NotImplementedError(f'Pattern {pattern} is not supported')
        #     # TODO: Requires equality to be implemented
        #     converted_pattern = Exists(0, prop.And(Implies(EVar(0), pattern), Implies(pattern, EVar(0))))
        #     subst_axioms.append(ConvertedAxiom(AxiomType.FunctionalSymbol, converted_pattern))
        return subst_axioms

    def _construct_event_axioms(self, hint: KoreHint) -> list[ConvertedAxiom]:
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
                rewrite_sort: KSort = self.get_sort(sort.name)
                left_rw_pattern = self._convert_pattern(left)
                right_rw_pattern = self._convert_pattern(right)

                return kl.KoreRewrites(rewrite_sort.aml_symbol, left_rw_pattern, right_rw_pattern)
            case kore.And(sort, left, right):
                and_sort: KSort = self.get_sort(sort.name)
                left_and_pattern: Pattern = self._convert_pattern(left)
                right_and_pattern: Pattern = self._convert_pattern(right)

                return kl.KoreAnd(and_sort.aml_symbol, left_and_pattern, right_and_pattern)
            case kore.Or(sort, left, right):
                or_sort: KSort = self.get_sort(sort.name)
                left_or_pattern: Pattern = self._convert_pattern(left)
                right_or_pattern: Pattern = self._convert_pattern(right)

                return kl.KoreOr(or_sort.aml_symbol, left_or_pattern, right_or_pattern)
            case kore.App(symbol, sorts, args):

                def chain_patterns(patterns: list[Pattern]) -> Pattern:
                    *patterns_left, next_one = patterns
                    if len(patterns_left) == 0:
                        return next_one
                    else:
                        return App(chain_patterns(patterns_left), next_one)

                if symbol in self._cell_symbols:

                    def is_cell(kore_application: kore.Pattern) -> str | None:
                        """Returns the cell name if the given application is a cell, None otherwise."""
                        if isinstance(kore_application, kore.App):
                            if comparison := match(r"Lbl'-LT-'(.+)'-GT-'", kore_application.symbol):
                                return comparison.group(0)
                        return None

                    def convert_cell(kore_application: kore.App) -> Pattern:
                        """Converts a cell to a pattern."""
                        cell_name = is_cell(kore_application)
                        assert cell_name, f'Application {kore_application} is not a cell!'

                        cell_symbol: Symbol = self.get_symbol(cell_name).aml_symbol
                        self._cell_symbols.add(kore_application.symbol)
                        if kore_application.symbol in self._raw_functional_symbols:
                            self._functional_symbols.add(cell_symbol)

                        if len(kore_application.args) == 0:
                            print(f'Cell {cell_name} has nothing to store!')
                            return cell_symbol
                        else:
                            chained_cell_patterns: list[Pattern] = []
                            for kore_pattern in kore_application.args:
                                if is_cell(kore_pattern):
                                    assert isinstance(kore_pattern, kore.App)
                                    converted_cell: Pattern = convert_cell(kore_pattern)
                                    chained_cell_patterns.append(converted_cell)
                                else:
                                    converted_value = self._convert_pattern(kore_pattern)
                                    chained_cell_patterns.append(converted_value)

                            # TODO: This is hacky, we will have a trouble if all cells are EVars or Metavars
                            cells_chained = chain_patterns(chained_cell_patterns)
                            if any(x for x in chained_cell_patterns if isinstance(x, kl.Cell)):
                                assert isinstance(cells_chained, App)
                                return kl.KoreNestedCells(cell_symbol, cells_chained)
                            else:
                                return kl.Cell(cell_symbol, cells_chained)

                    # Process cells
                    # We need them to be converted to a sequence: App (App(kcell, 1)) (App(scell, 2))
                    # Nested cells have a specific notation: Nested(tcell, App (App(kcell, 1)) (App(scell, 2)))
                    return convert_cell(pattern)
                else:
                    ksymbol: KSymbol = self.get_symbol(symbol)
                    # TODO: Use this after the new notation format is implemented
                    # aml_notation = ksymbol.aml_notation()
                    args_patterns: list[Pattern] = [self._convert_pattern(arg) for arg in args]
                    ksorts: list[KSort] = [self.get_sort(sort.name) for sort in sorts]
                    sorts_patterns: list[Pattern] = [ksort.aml_symbol for ksort in ksorts]

                    args_chain = chain_patterns([ksymbol.aml_symbol] + args_patterns)

                    application_sorts = sorts_patterns if sorts_patterns else [prop.Top()]
                    assert isinstance(args_chain, (App, Symbol))
                    return kl.KoreApplies(tuple(application_sorts), args_chain)
            case kore.EVar(name, _):
                # TODO: Revisit when we have sorting implemented!
                # return self._resolve_evar(pattern)
                return self._resolve_metavar(name)
            case kore.Top(sort):
                top_sort_symbol: Pattern = self.get_sort(sort.name).aml_symbol
                return kl.KoreTop(top_sort_symbol)
            case kore.DV(sort, value):
                dv_sort_symbol: Pattern = self.get_sort(sort.name).aml_symbol
                value_symbol: Pattern = Symbol(str(value.value))
                return kl.KoreDv(dv_sort_symbol, value_symbol)

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
