from __future__ import annotations

from dataclasses import dataclass, field
from enum import Enum
from itertools import count
from typing import TYPE_CHECKING, NamedTuple, ParamSpec, TypeVar

import pyk.kore.syntax as kore

import proof_generation.proofs.kore as kl
from proof_generation.pattern import App, EVar, Instantiate, MetaVar, Pattern, Symbol

if TYPE_CHECKING:
    from collections.abc import Callable
    from types import TracebackType

    from proof_generation.pattern import Notation, SVar

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


# TODO: Remove this class
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
        return Symbol('ksym_' + self.name)

    @staticmethod
    def unwrap_kore_name(sym: Symbol) -> str | None:
        if not sym.name.startswith('ksym_'):
            return None
        return sym.name.removeprefix('ksym_')

    @property
    def app(self) -> Notation:
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

    @property
    def requires(self) -> Pattern:
        requires, *_ = kl.deconstruct_equality_rule(self.pattern)
        return requires

    @property
    def left(self) -> Pattern:
        _, eq_left, *_ = kl.deconstruct_equality_rule(self.pattern)
        return eq_left

    @property
    def rhs_with_ensures(self) -> Pattern:
        _, _, implies_rhs, *_ = kl.deconstruct_equality_rule(self.pattern)
        return implies_rhs

    @property
    def right(self) -> Pattern:
        _, _, _, eq_right, _ = kl.deconstruct_equality_rule(self.pattern)
        return eq_right

    @property
    def ensures(self) -> Pattern:
        _, _, _, _, ensures = kl.deconstruct_equality_rule(self.pattern)
        return ensures

    @property
    def substitutions_from_requires(self) -> dict[int, Pattern]:
        """Collect substitutions from the requires part of the axiom introduced artificially by K."""
        substitutions: dict[int, Pattern] = {}

        def matching_clause(pattern: Pattern) -> None:
            if top_and_match := kl.kore_and.matches(pattern):
                _, left, right = top_and_match

                for item in (left, right):
                    if let_match := kl.equational_as.matches(item):
                        _, _, from_evar, to_evar, expression = let_match
                        if isinstance(from_evar, EVar) and isinstance(to_evar, EVar) and from_evar.name != to_evar.name:
                            substitutions[from_evar.name] = expression
                            substitutions[to_evar.name] = expression
                    elif in_match := kl.kore_in.matches(item):
                        _, _, var, expression = in_match
                        if isinstance(var, EVar):
                            substitutions[var.name] = expression
                    elif kl.kore_and.matches(item):
                        matching_clause(item)

        matching_clause(self.requires)

        return substitutions


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
    def equational_rule(self, pattern: Pattern) -> KEquationalRule:
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
    # TODO: This is temporary, we need to get rid of metavars used as EVars
    SORT_PARAM_METAVAR = 100

    def __init__(self) -> None:
        self._evars: dict[str, EVar] = {}
        self._svars: dict[str, SVar] = {}
        self._metavars: dict[str, MetaVar] = {}
        self._sort_param_metavars: dict[str, MetaVar] = {}

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

    def lookup_metavar(self, name: str) -> MetaVar:
        if name in self._metavars:
            return self._metavars[name]
        raise KeyError(f'Variable name {name} not found in meta vars dict!')

    def resolve_sort_param_metavar(self, name: str) -> MetaVar:
        """Resolve the metavar in the given pattern."""
        if name not in self._sort_param_metavars:
            self._sort_param_metavars[name] = MetaVar(name=self.SORT_PARAM_METAVAR + len(self._sort_param_metavars))
        return self._sort_param_metavars[name]

    def lookup_sort_param_metavar(self, name: str) -> MetaVar:
        """Keeping metavars for sort parameters separately from the other metavars."""
        if name in self._sort_param_metavars:
            return self._sort_param_metavars[name]
        raise KeyError(f'Variable name {name} not found in sort param meta vars dict!')


class LanguageSemantics(BuilderScope):
    def __init__(self) -> None:
        self._imported_modules: tuple[KModule, ...] = ()
        self._cached_axiom_scopes: dict[int, ConvertionScope] = {}
        self._inferred_notations: set[Notation] = set()

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
        notations = [sym.app for sym in symbols]

        return (*dict.fromkeys(notations), *self._inferred_notations)

    def __enter__(self) -> LanguageSemantics:
        """It is not allows to change the semantics except while parsing."""
        obj = super().__enter__()
        assert isinstance(obj, LanguageSemantics)
        return obj

    @staticmethod
    def is_rewrite_rule(pattern: kore.Pattern) -> bool:
        return (
            isinstance(pattern, kore.Rewrites)
            and isinstance(pattern.left, kore.And)
            and isinstance(pattern.right, kore.And)
        )

    @staticmethod
    def is_equational_rule(pattern: kore.Pattern) -> bool:
        return isinstance(pattern, kore.Implies) and (
            isinstance(pattern.right, kore.Equals)
            or (isinstance(pattern.right, kore.And) and any(isinstance(op, kore.Equals) for op in pattern.right.ops))
        )

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
                            if semantics.is_rewrite_rule(sentence.pattern):
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
                                rw_axiom = module.rewrite_rule(parsed_pattern)
                                semantics._cached_axiom_scopes[rw_axiom.ordinal] = scope
                            elif semantics.is_equational_rule(sentence.pattern):
                                pattern = sentence.pattern

                                scope = ConvertionScope()
                                parsed_pattern = semantics._convert_pattern(scope, pattern)
                                eq_axiom = module.equational_rule(parsed_pattern)
                                semantics._cached_axiom_scopes[eq_axiom.ordinal] = scope
                            else:
                                next(module.counter)
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
            # TODO: Replace it with the EVar later
            name = scope.lookup_metavar(var_name).name
            substitutions[name] = self._convert_pattern(scope, kore_pattern)
        return substitutions

    def count_simplifications(self, pattern: Pattern) -> int:
        """Count the number of function symbols in the given pattern (functional, not ctr, not cell)."""
        functional_symbols = 0

        def count_function_symbol(symbol: Symbol) -> None:
            ksymbol = self.resolve_to_ksymbol(symbol)
            if ksymbol is not None and ksymbol.is_functional and not ksymbol.is_cell and not ksymbol.is_ctor:
                nonlocal functional_symbols
                functional_symbols += 1

        if isinstance(pattern, Symbol):
            count_function_symbol(pattern)
        elif isinstance(pattern, App):
            symbol_pattern, args = kl.deconstruct_nary_application(pattern)
            if isinstance(symbol_pattern, Symbol):
                count_function_symbol(symbol_pattern)
            else:
                functional_symbols += self.count_simplifications(symbol_pattern)
            for arg in args:
                functional_symbols += self.count_simplifications(arg)
        elif isinstance(pattern, Instantiate):
            functional_symbols += self.count_simplifications(pattern.pattern)
            for inst in pattern.inst.values():
                functional_symbols += self.count_simplifications(inst)
        else:
            children = Pattern.unwrap(pattern)
            if children:
                for child in children:
                    functional_symbols += self.count_simplifications(child)
        return functional_symbols

    def _convert_sort(self, scope: ConvertionScope, sort: kore.Sort | kore.SortVar) -> Pattern:
        if isinstance(sort, kore.SortVar):
            return scope.resolve_sort_param_metavar(sort.name)
        else:
            return self.get_sort(sort.name).aml_symbol

    def _convert_pattern(self, scope: ConvertionScope, pattern: kore.Pattern) -> Pattern:
        """Convert the given pattern to the pattern in the new format."""
        match pattern:
            case kore.Rewrites(sort, left, right):
                rewrite_sort_pattern: Pattern = self._convert_sort(scope, sort)
                left_rw_pattern = self._convert_pattern(scope, left)
                right_rw_pattern = self._convert_pattern(scope, right)

                return kl.kore_rewrites(rewrite_sort_pattern, left_rw_pattern, right_rw_pattern)
            case kore.And(sort, ops):
                # TODO: generalize to more than two operands, if needed
                assert len(ops) == 2, f'Expected a kore "And" term with two operands, found one with {len(ops)}!'
                and_sort_pattern: Pattern = self._convert_sort(scope, sort)
                left_and_pattern: Pattern = self._convert_pattern(scope, ops[0])
                right_and_pattern: Pattern = self._convert_pattern(scope, ops[1])

                return kl.kore_and(and_sort_pattern, left_and_pattern, right_and_pattern)
            case kore.Or(sort, ops):
                # TODO: generalize to more than two operands, if needed
                assert len(ops) == 2, f'Expected a kore "Or" term with two operands, found one with {len(ops)}!'
                or_sort_pattern: Pattern = self._convert_sort(scope, sort)
                left_or_pattern: Pattern = self._convert_pattern(scope, ops[0])
                right_or_pattern: Pattern = self._convert_pattern(scope, ops[1])

                return kl.kore_or(or_sort_pattern, left_or_pattern, right_or_pattern)
            case kore.In(input_sort, output_sort, left, right):
                in_input_sort_pattern = self._convert_sort(scope, input_sort)
                in_output_sort_pattern = self._convert_sort(scope, output_sort)
                left_in_pattern = self._convert_pattern(scope, left)
                right_in_pattern = self._convert_pattern(scope, right)

                return kl.kore_in(in_input_sort_pattern, in_output_sort_pattern, left_in_pattern, right_in_pattern)
            case kore.Not(sort, op):
                not_sort_pattern: Pattern = self._convert_sort(scope, sort)
                not_op_pattern: Pattern = self._convert_pattern(scope, op)

                return kl.kore_not(not_sort_pattern, not_op_pattern)
            case kore.Next(sort, op):
                next_sort_pattern: Pattern = self._convert_sort(scope, sort)
                next_op_pattern: Pattern = self._convert_pattern(scope, op)

                return kl.kore_next(next_sort_pattern, next_op_pattern)
            case kore.Implies(sort, left, right):
                implies_sort_pattern: Pattern = self._convert_sort(scope, sort)
                implies_left: Pattern = self._convert_pattern(scope, left)
                implies_right: Pattern = self._convert_pattern(scope, right)

                return kl.kore_implies(implies_sort_pattern, implies_left, implies_right)
            case kore.Ceil(input_sort, output_sort, pattern):
                ceil_input_sort_pattern: Pattern = self._convert_sort(scope, input_sort)
                ceil_output_sort_pattern: Pattern = self._convert_sort(scope, output_sort)
                ceil_pattern: Pattern = self._convert_pattern(scope, pattern)

                return kl.kore_ceil(ceil_input_sort_pattern, ceil_output_sort_pattern, ceil_pattern)
            case kore.Floor(input_sort, output_sort, pattern):
                floor_input_sort_pattern: Pattern = self._convert_sort(scope, input_sort)
                floor_output_sort_pattern: Pattern = self._convert_sort(scope, output_sort)
                floor_pattern: Pattern = self._convert_pattern(scope, pattern)

                return kl.kore_floor(floor_input_sort_pattern, floor_output_sort_pattern, floor_pattern)
            case kore.Iff(sort, left, right):
                iff_sort_pattern: Pattern = self._convert_sort(scope, sort)
                left_iff_pattern: Pattern = self._convert_pattern(scope, left)
                right_iff_pattern: Pattern = self._convert_pattern(scope, right)

                return kl.kore_iff(iff_sort_pattern, left_iff_pattern, right_iff_pattern)
            case kore.Equals(input_sort, output_sort, left, right):
                equals_input_sort_pattern = self._convert_sort(scope, input_sort)
                equals_sort_pattern: Pattern = self._convert_sort(scope, output_sort)
                equals_left: Pattern = self._convert_pattern(scope, left)
                equals_right: Pattern = self._convert_pattern(scope, right)

                return kl.kore_equals(equals_input_sort_pattern, equals_sort_pattern, equals_left, equals_right)
            case kore.App(symbol, ksorts, args):
                ksymbol: KSymbol = self.get_symbol(symbol)
                sort_params: list[Pattern] = [self._convert_sort(scope, sort) for sort in ksorts]
                arg_patterns: list[Pattern] = [self._convert_pattern(scope, arg) for arg in args]

                return ksymbol.app(*(sort_params + arg_patterns))
            case kore.EVar(name, _):
                # TODO: Revisit when we have sorting implemented!
                # return scope.resolve_evar(pattern)
                return scope.resolve_metavar(name)
            case kore.SVar(name, sort):
                raise NotImplementedError()
            case kore.Top(sort):
                top_sort_pattern: Pattern = self._convert_sort(scope, sort)
                return kl.kore_top(top_sort_pattern)
            case kore.Bottom(sort):
                bottom_sort_pattern = self._convert_sort(scope, sort)
                return kl.kore_bottom(bottom_sort_pattern)
            case kore.DV(sort, value):
                dv_sort_pattern: Pattern = self._convert_sort(scope, sort)
                value_symbol: Pattern = Symbol(str(value.value))
                return kl.kore_dv(dv_sort_pattern, value_symbol)
            case kore.Exists(sort, var, pattern):
                exists_inner_sort_pattern: Pattern = self._convert_sort(scope, var.sort)
                exists_outer_sort_pattern: Pattern = self._convert_sort(scope, sort)
                exists_var_pattern: Pattern = self._convert_pattern(scope, var)
                exists_pattern: Pattern = self._convert_pattern(scope, pattern)
                # TODO: This should be fixed after functional substitution is implemented
                # assert isinstance(exists_var_pattern, EVar | SVar)
                assert isinstance(exists_var_pattern, MetaVar)

                custom_exists_notation = kl.kore_exists(exists_var_pattern.name)
                self._inferred_notations.add(custom_exists_notation)
                return custom_exists_notation(exists_inner_sort_pattern, exists_outer_sort_pattern, exists_pattern)
            case kore.Forall(output_sort, var, pattern):
                raise NotImplementedError()
            case kore.Mu(var, pattern):
                raise NotImplementedError()
            case kore.Nu(var, pattern):
                raise NotImplementedError()
        raise NotImplementedError(f'Pattern {pattern} is not supported')
