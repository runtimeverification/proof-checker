from __future__ import annotations


import proof_generation.pattern as nf
from mm_transfer.converter.vardict import Vardict
from mm_transfer.metamath.ast import Metavariable, Term


class Scope:

    def __init__(self, essential_conditions: tuple[Term] | None = None, previous_scope: Scope | None = None) -> None:
        self._metavars: Vardict = Vardict(None, nf.MetaVar)
        self._symbols: Vardict = Vardict(None, nf.Symbol)
        self._element_vars: Vardict = Vardict(None, nf.EVar)
        self._set_vars: Vardict = Vardict(None, nf.SVar)
        self._domain_values: set[str] = set()

        if previous_scope is not None:
            self._import_previous_scope(previous_scope)
        if essential_conditions:
            self._process_essential_conditions()

    def add_metavariable(self, var: Metavariable) -> None:
        self._metavars[var.name] = nf.MetaVar(len(self._metavars))

    def add_symbol(self, var: Metavariable) -> None:
        self._symbols[var.name] = nf.Symbol(len(self._symbols))

    def add_element_var(self, var: Metavariable) -> None:
        self._element_vars[var.name] = nf.EVar(len(self._element_vars))

    def add_set_var(self, var: Metavariable) -> None:
        self._set_vars[var.name] = nf.SVar(len(self._set_vars))

    def add_domain_value(self, cnst: str) -> None:
        self._domain_values.add(cnst)

    def _import_previous_scope(self, previous_scope: Scope) -> None:
        pass

    def _process_essential_conditions(self) -> None:
        pass
