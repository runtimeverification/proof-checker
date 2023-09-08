from __future__ import annotations

import re
from typing import TYPE_CHECKING

from mm_transfer.metamath.ast import (
    Application,
    AxiomaticStatement,
    ConstantStatement,
    FloatingStatement,
    Metavariable,
    VariableStatement,
)

if TYPE_CHECKING:
    from mm_transfer.metamath.ast import Database
    from proof_generation.proof import BasicInterpreter


class MetamathConverter:
    """
    Get the parsed object and try to convert it making as few iterations as possible
    """

    def __init__(self, parsed: Database) -> None:
        self.parsed = parsed
        self._declared_constants: set[str] = set()
        self._declared_variables: dict[str, Metavariable] = {}
        self._patterns: dict[str, Metavariable] = {}
        self._symbols: dict[str, Metavariable] = {}
        self._variables: dict[str, Metavariable] = {}
        self._element_vars: dict[str, Metavariable] = {}
        self._set_vars: dict[str, Metavariable] = {}
        self._domain_values: set[str] = set()
        self._top_down()

    def put_vars_on_stack(self, interpreter: BasicInterpreter) -> None:
        """
        Put all the variables on the stack
        """
        for cnt, var in enumerate(self._symbols.values()):
            print(f'var {var.name} as Symbol with id {cnt}')
            interpreter.symbol(cnt)

        for cnt, var in enumerate(self._patterns.values()):
            print(f'var {var.name} as Metavariable with id {cnt}')
            interpreter.metavar(cnt)

    def _top_down(self) -> None:
        """
        Convert the database from top to bottom
        """
        for statement in self.parsed.statements:
            if isinstance(statement, ConstantStatement):
                self._import_constants(statement)
            if isinstance(statement, VariableStatement):
                self._import_variables(statement)
            elif isinstance(statement, FloatingStatement):
                self._import_floating(statement)
            elif isinstance(statement, AxiomaticStatement):
                self._import_axioms(statement)
            else:
                continue

    def _import_constants(self, statement: ConstantStatement) -> None:
        self._declared_constants.update(set(statement.constants))

    def _import_variables(self, statement: VariableStatement) -> None:
        for var in statement.metavariables:
            self._declared_variables[var.name] = var

    def _import_axioms(self, statement: AxiomaticStatement) -> None:
        is_constant = re.compile(r'"\S+"')

        def constant_is_pattern_axiom(st: AxiomaticStatement) -> bool:
            if (
                isinstance(st.terms[0], Application)
                and st.terms[0].symbol == '#Pattern'
                and isinstance(st.terms[1], Application)
                and st.terms[1].symbol in self._declared_constants
                and is_constant.match(st.terms[1].symbol)
            ):
                # We can distinguish domain values from other constants, but we decided
                # to keep quotes in favor of the direct correspondence between Metamath
                # and the new format.
                self._domain_values.add(st.terms[1].symbol)
                return True
            else:
                return False

        # TODO: Replace the single call according to further needs on the next step
        constant_is_pattern_axiom(statement)

    def _import_floating(self, statement: FloatingStatement) -> None:
        def get_pattern(st: FloatingStatement) -> Metavariable | None:
            if (
                isinstance(st.terms[0], Application)
                and st.terms[0].symbol == '#Pattern'
                and isinstance(st.terms[1], Metavariable)
                and st.terms[1].name in self._declared_variables
            ):
                return self._declared_variables[st.terms[1].name]
            else:
                return None

        def get_symbol(st: FloatingStatement) -> Metavariable | None:
            if (
                isinstance(st.terms[0], Application)
                and st.terms[0].symbol == '#Symbol'
                and isinstance(st.terms[1], Metavariable)
                and st.terms[1].name in self._declared_variables
            ):
                return self._declared_variables[st.terms[1].name]
            else:
                return None

        def get_var(st: FloatingStatement) -> Metavariable | None:
            if (
                isinstance(st.terms[0], Application)
                and st.terms[0].symbol == '#Variable'
                and isinstance(st.terms[1], Metavariable)
                and st.terms[1].name in self._declared_variables
            ):
                return self._declared_variables[st.terms[1].name]
            else:
                return None

        def get_element_var(st: FloatingStatement) -> Metavariable | None:
            if (
                isinstance(st.terms[0], Application)
                and st.terms[0].symbol == '#ElementVariable'
                and isinstance(st.terms[1], Metavariable)
                and st.terms[1].name in self._declared_variables
            ):
                return self._declared_variables[st.terms[1].name]
            else:
                return None

        def get_set_var(st: FloatingStatement) -> Metavariable | None:
            if (
                isinstance(st.terms[0], Application)
                and st.terms[0].symbol == '#SetVariable'
                and isinstance(st.terms[1], Metavariable)
                and st.terms[1].name in self._declared_variables
            ):
                return self._declared_variables[st.terms[1].name]
            else:
                return None

        if var := get_pattern(statement):
            self._patterns[var.name] = var
        elif var := get_symbol(statement):
            self._symbols[var.name] = var
        elif var := get_var(statement):
            self._variables[var.name] = var
        elif var := get_element_var(statement):
            self._element_vars[var.name] = var
        elif var := get_set_var(statement):
            self._set_vars[var.name] = var
        else:
            print(f'Unknown floating statement: {repr(statement)}')
