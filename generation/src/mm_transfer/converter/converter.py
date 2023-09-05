from __future__ import annotations

from typing import TYPE_CHECKING

from mm_transfer.metamath.ast import Application, FloatingStatement, Metavariable, VariableStatement

if TYPE_CHECKING:
    from mm_transfer.metamath.ast import Database
    from proof_generation.proof import BasicInterpreter


class MetamathConverter:
    """
    Get the parsed object and try to convert it making as few iterations as possible
    """

    def __init__(self, parsed: Database) -> None:
        self.parsed = parsed
        self._declared_variables: dict[str, Metavariable] = {}
        self._patterns: dict[str, Metavariable] = {}
        self._symbols: dict[str, Metavariable] = {}
        self._variables: dict[str, Metavariable] = {}
        self._element_vars: dict[str, Metavariable] = {}
        self._set_vars: dict[str, Metavariable] = {}
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
