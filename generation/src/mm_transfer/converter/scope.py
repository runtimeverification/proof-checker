from __future__ import annotations

from copy import deepcopy
from typing import TYPE_CHECKING

from mypy_extensions import VarArg

import proof_generation.pattern as nf
from mm_transfer.converter.vardict import VarDict
from mm_transfer.metamath.ast import Metavariable

if TYPE_CHECKING:
    from collections.abc import Callable

    from mm_transfer.metamath.ast import Term


class Scope:
    def __init__(
        self,
        essential_conditions: tuple[Term, ...] | None = None,
        previous_scope: Scope | None = None,
        args: tuple[str, ...] | None = None,
    ) -> None:
        self._metavars: VarDict = VarDict(None, nf.MetaVar)
        self._symbols: VarDict = VarDict(None, nf.Symbol)
        self._element_vars: VarDict = VarDict(None, nf.EVar)
        self._set_vars: VarDict = VarDict(None, nf.SVar)
        self._domain_values: set[str] = set()
        self._args: tuple[str, ...] | None = args

        if previous_scope is not None:
            self._import_previous_scope(previous_scope)
        if essential_conditions:
            self._process_essential_conditions()

    def add_metavariable(self, var: Metavariable) -> None:
        self._metavars[var.name] = nf.MetaVar(len(self._metavars))

    def add_symbol(self, var: Metavariable | str) -> None:
        if isinstance(var, Metavariable):
            self._symbols[var.name] = nf.Symbol(len(self._symbols))
        else:
            self._symbols[var] = nf.Symbol(len(self._symbols))

    def add_element_var(self, var: Metavariable) -> None:
        self._element_vars[var.name] = nf.EVar(len(self._element_vars))

    def add_set_var(self, var: Metavariable) -> None:
        self._set_vars[var.name] = nf.SVar(len(self._set_vars))

    def add_domain_value(self, cnst: str) -> None:
        self._domain_values.add(cnst)

    def resolve(self, name: str) -> Callable[[VarArg(nf.Pattern)], nf.Pattern]:
        if isinstance(self._args, tuple) and name in self._args:

            def match_arg(*args: nf.Pattern) -> nf.Pattern:
                # Can be rewritten as lambda but Typechecker requires a couple of assertions
                assert isinstance(self._args, tuple) and name in self._args
                position: int = self._args.index(name)
                assert len(args) > position
                return args[position]

            return match_arg
        elif name in self._metavars:
            var = self._metavars[name]
        elif name in self._symbols:
            var = self._symbols[name]
        elif name in self._element_vars:
            var = self._element_vars[name]
        elif name in self._set_vars:
            var = self._set_vars[name]
        else:
            raise KeyError(f'Unknown variable {name}')

        return lambda *args: var

    def is_symbol(self, name: str) -> bool:
        return name in self._symbols

    def _import_previous_scope(self, previous_scope: Scope) -> None:
        pass

    def _process_essential_conditions(self) -> None:
        pass

    def _reduce_to_args(self, args: tuple[Metavariable, ...]) -> Scope:
        copied = deepcopy(self)
        assert all(isinstance(arg, Metavariable) for arg in args)
        arg_names = tuple(arg.name for arg in args)
        for name in self._metavars:
            if name not in arg_names:
                del copied._metavars[name]
        copied._args = arg_names
        return copied
