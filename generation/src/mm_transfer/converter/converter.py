from __future__ import annotations

from typing import TYPE_CHECKING

from mm_transfer.metamath.ast import Application, FloatingStatement, Metavariable, VariableStatement

if TYPE_CHECKING:
    from mm_transfer.metamath.ast import Database
    from proof_generation.proof import BasicInterpreter


class MetamathConverter:
    """
    Get the parsed object and try to convert it making as less iterations as possible
    """

    def __init__(self, parsed: Database) -> None:
        self.parsed = parsed
        self._declared_variables: dict[str, Metavariable] = {}
        self._patterns: dict[str, Metavariable] = {}
        self._symbols: dict[str, Metavariable] = {}
        self._variables: dict[str, Metavariable] = {}
        self._elemental: dict[str, Metavariable] = {}
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
            if isinstance(statement, VariableStatement):
                self._import_variables(statement)
            elif isinstance(statement, FloatingStatement):
                self._import_floating(statement)
            else:
                continue

    def _import_variables(self, statement: VariableStatement) -> None:
        for var in statement.metavariables:
            self._declared_variables[var.name] = var

    def _import_floating(self, statement: FloatingStatement) -> None:
        var: Metavariable | None = None

        def is_pattern(st: FloatingStatement) -> bool:
            if (
                isinstance(st.terms[0], Application)
                and st.terms[0].symbol == '#Pattern'
                and isinstance(st.terms[1], Metavariable)
                and st.terms[1].name in self._declared_variables
            ):
                nonlocal var
                var = self._declared_variables[st.terms[1].name]
                return True
            return False

        def is_symbol(st: FloatingStatement) -> bool:
            if (
                isinstance(st.terms[0], Application)
                and st.terms[0].symbol == '#Symbol'
                and isinstance(st.terms[1], Metavariable)
                and st.terms[1].name in self._declared_variables
            ):
                nonlocal var
                var = self._declared_variables[st.terms[1].name]
                return True
            return False

        def is_var(st: FloatingStatement) -> bool:
            if (
                isinstance(st.terms[0], Application)
                and st.terms[0].symbol == '#Variable'
                and isinstance(st.terms[1], Metavariable)
                and st.terms[1].name in self._declared_variables
            ):
                nonlocal var
                var = self._declared_variables[st.terms[1].name]
                return True
            return False

        def is_element_var(st: FloatingStatement) -> bool:
            if (
                isinstance(st.terms[0], Application)
                and st.terms[0].symbol == '#ElementVariable'
                and isinstance(st.terms[1], Metavariable)
                and st.terms[1].name in self._declared_variables
            ):
                nonlocal var
                var = self._declared_variables[st.terms[1].name]
                return True
            return False

        if is_pattern(statement) and var is not None:
            self._patterns[var.name] = var
        elif is_symbol(statement) and var is not None:
            self._symbols[var.name] = var
        elif is_var(statement) and var is not None:
            self._variables[var.name] = var
        elif is_element_var(statement) and var is not None:
            self._elemental[var.name] = var
        else:
            print(f'Unknown floating statement: {repr(statement)}')
