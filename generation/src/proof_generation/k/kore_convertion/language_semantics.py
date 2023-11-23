from __future__ import annotations

from dataclasses import dataclass, field
from enum import Enum
from itertools import count
from typing import TYPE_CHECKING, NamedTuple, ParamSpec, TypeVar

import pyk.kore.syntax as kore

import proof_generation.proofs.kore as kl
from proof_generation.pattern import EVar, MetaVar, Symbol

if TYPE_CHECKING:
    from collections.abc import Callable
    from types import TracebackType

    from proof_generation.pattern import Notation, Pattern, SVar

T = TypeVar('T')
P = ParamSpec('P')


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


@dataclass(frozen=True)
class KSortVar:
    name: str


@dataclass(frozen=True)
class KSymbol:
    name: str
    sort_params: tuple[KSortVar, ...]
    output_sort: KSort | KSortVar
    input_sorts: tuple[KSort | KSortVar, ...] = field(default_factory=tuple)
    is_functional: bool = False
    is_ctor: bool = False
    is_cell: bool = False

    @property
    def aml_symbol(self) -> Symbol:
        return Symbol('kore_' + self.name)

    @staticmethod
    def unwrap_kore_name(sym: Symbol) -> str | None:
        if not sym.name.startswith('kore_'):
            return None
        return sym.name.removeprefix('kore_')

    @property
    def aml_notation(self) -> Notation:
        if self.name == 'kseq':
            return kl.kore_kseq
        else:
            return kl.nary_app(self.aml_symbol, len(self.sort_params) + len(self.input_sorts), self.is_cell)


@dataclass(frozen=True)
class KRewritingRule:
    ordinal: int
    pattern: Pattern


@dataclass(frozen=True)
class KEquationalRule:
    ordinal: int
    pattern: Pattern


class BuilderScope:
    def __init__(self) -> None:
        self._parsing = False

    def __enter__(self) -> BuilderScope:
        """It is not allows to change the semantics except while parsing."""
        self._parsing = True
        return self

    def __exit__(
        self,
        exc_type: type[BaseException] | None,
        exc_value: BaseException | None,
        traceback: TracebackType | None,
    ) -> None:
        """It is not allows to change the semantics except while parsing."""
        self._parsing = False


def builder_method(func: Callable[P, T]) -> Callable[P, T]:
    """Helps to forbid calling methods that c   hange the semantics outside of parsing."""

    def wrapper(*args: P.args, **kwargs: P.kwargs) -> T:
        assert len(args) > 0
        first_arg = args[0]
        assert isinstance(first_arg, BuilderScope)
        if first_arg._parsing:
            return func(*args, **kwargs)
        else:
            raise ValueError('Cannot call parsing method on immutable theory')

    return wrapper


class KModule(BuilderScope):
    def __init__(self, name: str, counter: count) -> None:
        self._name = name
        self.counter = counter

        # Ordinal -> axiom
        self._imported_modules: tuple[KModule, ...] = ()
        self._sorts: dict[str, KSort] = {}
        self._symbols: dict[str, KSymbol] = {}
        self._axioms: dict[int, KRewritingRule | KEquationalRule] = {}

    def __enter__(self) -> KModule:
        """It is not allows to change the semantics except while parsing."""
        obj = super().__enter__()
        assert isinstance(obj, KModule)
        return obj

    @property
    def name(self) -> str:
        return self._name

    @property
    def sorts(self) -> tuple[KSort, ...]:
        sorts = list(self._sorts.values())
        for module in self.modules:
            sorts.extend(module.sorts)

        # Ordering and removing duplicated
        return tuple(dict.fromkeys(sorts))

    @property
    def symbols(self) -> tuple[KSymbol, ...]:
        symbols = list(self._symbols.values())
        for module in self.modules:
            symbols.extend(module.symbols)

        # Ordering and removing duplicated
        return tuple(dict.fromkeys(symbols))

    @property
    def modules(self) -> tuple[KModule, ...]:
        modules = []
        for module in self._imported_modules:
            modules.append(module)
            modules.extend(module.modules)
        # Ordering nd removing duplicated
        return tuple(dict.fromkeys(modules))

    @builder_method
    def import_module(self, module: KModule) -> None:
        if module in self._imported_modules:
            raise ValueError(f'Sort {module.name} already exists!')
        self._imported_modules += (module,)

    @builder_method
    def sort(self, name: str) -> KSort:
        return self._sort(name, False)

    @builder_method
    def hooked_sort(self, name: str) -> KSort:
        return self._sort(name, True)

    def _sort(self, name: str, hooked: bool) -> KSort:
        if name in self._sorts:
            raise ValueError(f'Sort {name} has been already added!')

        self._sorts[name] = KSort(name, hooked)
        return self._sorts[name]

    @builder_method
    def symbol(
        self,
        name: str,
        output_sort: KSort | KSortVar,
        *,  # Force to use named parameters
        sort_params: tuple[KSortVar, ...] = (),
        input_sorts: tuple[KSort | KSortVar, ...] = (),
        is_functional: bool = False,
        is_ctor: bool = False,
        is_cell: bool = False,
    ) -> KSymbol:
        if name in self._symbols:
            raise ValueError(f'Symbol {name} has been already added!')
        if isinstance(output_sort, KSort):
            # It should be either in the module or in imported modules
            assert self.get_sort(output_sort.name) == output_sort
        for sort in input_sorts:
            assert isinstance(sort, (KSort, KSortVar))
            if isinstance(sort, KSort):
                # It should be either in the module or in imported modules
                assert self.get_sort(sort.name) == sort

        symbol = KSymbol(name, sort_params, output_sort, input_sorts, is_functional, is_ctor, is_cell)
        self._symbols[name] = symbol
        return symbol

    @builder_method
    def equational_rewrite(self, pattern: Pattern) -> KEquationalRule:
        ordinal = next(self.counter)
        axiom = KEquationalRule(ordinal, pattern)
        self._axioms[ordinal] = axiom
        return axiom

    @builder_method
    def rewrite_rule(self, pattern: Pattern) -> KRewritingRule:
        ordinal = next(self.counter)
        axiom = KRewritingRule(ordinal, pattern)
        self._axioms[ordinal] = axiom
        return axiom

    def get_module(self, name: str) -> KModule:
        for module in self.modules:
            if module.name == name:
                return module
        raise ValueError(f'Module {name} not found')

    def get_sort(self, name: str) -> KSort:
        if name in self._sorts:
            return self._sorts[name]

        for module in self.modules:
            try:
                sort = module.get_sort(name)
                return sort
            except ValueError:
                continue
        raise ValueError(f'Sort {name} not found in the module {self.name}')

    def get_symbol(self, name: str) -> KSymbol:
        if name in self._symbols:
            return self._symbols[name]
        for module in self.modules:
            try:
                symbol = module.get_symbol(name)
                return symbol
            except ValueError:
                continue
        raise ValueError(f'Symbol {name} not found in the module {self.name}')

    def get_axiom(self, ordinal: int) -> KRewritingRule | KEquationalRule:
        if ordinal in self._axioms:
            return self._axioms[ordinal]

        for module in self.modules:
            try:
                axiom = module.get_axiom(ordinal)
                return axiom
            except ValueError:
                continue
        raise ValueError(f'Axiom with ordinal {ordinal} not found in the module {self.name}')


class ConvertionScope:
    def __init__(self) -> None:
        self._evars: dict[str, EVar] = {}
        self._svars: dict[str, SVar] = {}
        self._metavars: dict[str, MetaVar] = {}

    def resolve_evar(self, name: str) -> EVar:
        """Resolve the evar in the given pattern."""
        if name not in self._evars:
            self._evars[name] = EVar(name=len(self._evars))
        return self._evars[name]

    def resolve_metavar(self, name: str) -> MetaVar:
        """Resolve the metavar in the given pattern."""
        if name not in self._metavars:
            self._metavars[name] = MetaVar(name=len(self._metavars))
        return self._metavars[name]

    def lookup_evar(self, name: str) -> EVar:
        assert name in self._evars.keys(), f'Variable name {name} not found in eVars dict!'
        return self._evars[name]


class LanguageSemantics(BuilderScope):
    def __init__(self) -> None:
        self._imported_modules: tuple[KModule, ...] = ()
        self._cached_axiom_scopes: dict[int, ConvertionScope] = {}

    @property
    def modules(self) -> tuple[KModule, ...]:
        modules = set()
        for module in self._imported_modules:
            modules.add(module)
            modules.update(module.modules)
        # Ordering and removing duplicated
        return tuple(dict.fromkeys(modules))

    @property
    def sorts(self) -> tuple[KSort, ...]:
        sorts: list[KSort] = []
        for module in self.modules:
            sorts.extend(module.sorts)

        # Ordering and removing duplicated
        return tuple(dict.fromkeys(sorts))

    @property
    def symbols(self) -> tuple[KSymbol, ...]:
        symbols: list[KSymbol] = []
        for module in self.modules:
            symbols.extend(module.symbols)

        # Ordering and removing duplicated
        return tuple(dict.fromkeys(symbols))

    @property
    def main_module(self) -> KModule:
        # TODO: This is a heuristic
        if len(self._imported_modules) == 0:
            raise ValueError('No modules have been added')
        return self._imported_modules[-1]

    @property
    def notations(self) -> tuple[Notation, ...]:
        symbols = self.symbols
        notations = [sym.aml_notation for sym in symbols]

        return tuple(dict.fromkeys(notations))

    def __enter__(self) -> LanguageSemantics:
        """It is not allows to change the semantics except while parsing."""
        obj = super().__enter__()
        assert isinstance(obj, LanguageSemantics)
        return obj

    @staticmethod
    def from_kore_definition(kore_definition: kore.Definition) -> LanguageSemantics:
        """Create a new instance of LanguageSemantics from the given Kore definition."""
        with LanguageSemantics() as semantics:
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

                            def convert_ksort(
                                name_to_sortvar: dict[str, KSortVar], ksort: kore.Sort
                            ) -> KSort | KSortVar:
                                match ksort:
                                    case kore.SortVar(name):
                                        return name_to_sortvar[name]
                                    case kore.SortApp(name):
                                        return module.get_sort(name)
                                    case _:
                                        raise NotImplementedError(f'Sort {repr(ksort)} is not supported')

                            ksort_params = tuple(KSortVar(v.name) for v in sentence.symbol.vars)
                            ksort_var_map = {v.name: v for v in ksort_params}

                            symbol = sentence.symbol.name
                            input_sorts: tuple[KSort | KSortVar, ...] = tuple(
                                convert_ksort(ksort_var_map, ksort) for ksort in sentence.param_sorts
                            )
                            output_sort: KSort | KSortVar = convert_ksort(ksort_var_map, sentence.sort)
                            attrs = [attr.symbol for attr in sentence.attrs if isinstance(attr, kore.App)]

                            # TODO: Support cells
                            module.symbol(
                                symbol,
                                output_sort,
                                sort_params=ksort_params,
                                input_sorts=input_sorts,
                                is_functional='functional' in attrs,
                                is_ctor='constructor' in attrs,
                                is_cell='cell' in attrs,
                            )
                        elif isinstance(sentence, kore.Axiom):
                            # Add axioms
                            if isinstance(sentence.pattern, kore.Rewrites):
                                pattern = sentence.pattern
                                assert isinstance(pattern, kore.Rewrites)
                                assert isinstance(pattern.left, kore.And)
                                assert isinstance(pattern.right, kore.And)

                                # TODO: Remove side conditions for now
                                preprocessed_pattern = kore.Rewrites(
                                    pattern.sort, pattern.left.ops[0], pattern.right.ops[0]
                                )
                                scope = ConvertionScope()
                                parsed_pattern = semantics._convert_pattern(scope, preprocessed_pattern)
                                axiom = module.rewrite_rule(parsed_pattern)
                                semantics._cached_axiom_scopes[axiom.ordinal] = scope
                            else:
                                next(module.counter)
                            # TODO: Cannot parse everything yet
                            # elif isinstance(sentence.pattern, kore.Equals):
                            #     parsed_pattern = semantics._convert_pattern(sentence.pattern)
                            #     module.equational_rewrite(parsed_pattern)

            return semantics

    @builder_method
    def module(self, name: str) -> KModule:
        if name in (module.name for module in self._imported_modules):
            raise ValueError(f'Module {name} has been already added')
        axiom_counter = count() if len(self._imported_modules) == 0 else self.main_module.counter

        module = KModule(name, axiom_counter)
        self._imported_modules += (module,)
        return module

    def get_module(self, name: str) -> KModule:
        for module in self.modules:
            if module.name == name:
                return module
        raise ValueError(f'Module {name} not found')

    def get_axiom(self, ordinal: int) -> KRewritingRule | KEquationalRule:
        return self.main_module.get_axiom(ordinal)

    def get_sort(self, name: str) -> KSort:
        # Reversing is done for optimization purposes, as we start the search with the main module
        for module in reversed(self.modules):
            assert isinstance(module, KModule)  # Oh, typechecker...
            try:
                sort = module.get_sort(name)
                return sort
            except ValueError:
                continue
        raise ValueError(f'Sort {name} not found')

    def get_symbol(self, name: str) -> KSymbol:
        for module in reversed(self.modules):
            assert isinstance(module, KModule)  # Oh, typechecker...
            try:
                symbol = module.get_symbol(name)
                return symbol
            except ValueError:
                continue
        raise ValueError(f'Sort {name} not found')

    def resolve_to_ksymbol(self, symbol: Symbol) -> KSymbol | None:
        kore_name = KSymbol.unwrap_kore_name(symbol)
        if kore_name is None:
            return None
        try:
            return self.get_symbol(kore_name)
        except ValueError:
            return None

    def convert_pattern(self, pattern: kore.Pattern) -> Pattern:
        """Convert the given pattern to the pattern in the new format."""
        scope = ConvertionScope()
        return self._convert_pattern(scope, pattern)

    def convert_substitutions(self, subst: dict[str, kore.Pattern], axiom_ordinal: int) -> dict[int, Pattern]:
        substitutions = {}
        scope = self._cached_axiom_scopes[axiom_ordinal]
        for var_name, kore_pattern in subst.items():
            name = scope.lookup_evar(var_name).name
            substitutions[name] = self._convert_pattern(scope, kore_pattern)
        return substitutions

    def _convert_pattern(self, scope: ConvertionScope, pattern: kore.Pattern) -> Pattern:
        """Convert the given pattern to the pattern in the new format."""
        match pattern:
            case kore.Rewrites(sort, left, right):
                rewrite_sort: KSort = self.get_sort(sort.name)
                left_rw_pattern = self._convert_pattern(scope, left)
                right_rw_pattern = self._convert_pattern(scope, right)

                return kl.kore_rewrites(rewrite_sort.aml_symbol, left_rw_pattern, right_rw_pattern)
            case kore.And(sort, ops):
                # TODO: generalize to more than two operands, if needed
                assert len(ops) == 2, f'Expected a kore "And" term with two operands, found one with {len(ops)}!'
                and_sort: KSort = self.get_sort(sort.name)
                left_and_pattern: Pattern = self._convert_pattern(scope, ops[0])
                right_and_pattern: Pattern = self._convert_pattern(scope, ops[1])

                return kl.kore_and(and_sort.aml_symbol, left_and_pattern, right_and_pattern)
            case kore.Or(sort, ops):
                # TODO: generalize to more than two operands, if needed
                assert len(ops) == 2, f'Expected a kore "Or" term with two operands, found one with {len(ops)}!'
                or_sort: KSort = self.get_sort(sort.name)
                left_or_pattern: Pattern = self._convert_pattern(scope, ops[0])
                right_or_pattern: Pattern = self._convert_pattern(scope, ops[1])

                return kl.kore_or(or_sort.aml_symbol, left_or_pattern, right_or_pattern)
            case kore.App(symbol, ksorts, args):
                ksymbol: KSymbol = self.get_symbol(symbol)
                sort_params: list[Pattern] = [self.get_sort(sort.name).aml_symbol for sort in ksorts]
                arg_patterns: list[Pattern] = [self._convert_pattern(scope, arg) for arg in args]

                return ksymbol.aml_notation(*(sort_params + arg_patterns))
            case kore.EVar(name, _):
                return scope.resolve_evar(name)
            case kore.Top(sort):
                top_sort_symbol: Pattern = self.get_sort(sort.name).aml_symbol
                return kl.kore_top(top_sort_symbol)
            case kore.DV(sort, value):
                dv_sort_symbol: Pattern = self.get_sort(sort.name).aml_symbol
                value_symbol: Pattern = Symbol(str(value.value))
                return kl.kore_dv(dv_sort_symbol, value_symbol)

        raise NotImplementedError(f'Pattern {pattern} is not supported')
