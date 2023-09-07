from __future__ import annotations
import re
from typing import TYPE_CHECKING, Callable

from mm_transfer.metamath.ast import (
    Application,
    AxiomaticStatement,
    ConstantStatement,
    FloatingStatement,
    Metavariable,
    VariableStatement,
)
from mm_transfer.converter.scope import Scope
import proof_generation.pattern as nf


if TYPE_CHECKING:
    from mm_transfer.metamath.ast import Database, Term
    from proof_generation.proof import BasicInterpreter


class MetamathConverter:
    """
    Get the parsed object and try to convert it making as few iterations as possible
    """

    def __init__(self, parsed: Database) -> None:
        self.parsed = parsed
        self._scope = Scope()
        self._declared_constants: set[str] = set()
        self._declared_variables: dict[str, Metavariable] = {}
        self._notations: dict[str, Callable] = {}

        # Add special cases that formalized in the new format differently
        self._add_builin_notations()

        # Go over all statements 1 by 1
        self._top_down()

    def put_vars_on_stack(self, interpreter: BasicInterpreter) -> None:
        """
        Put all the variables on the stack
        """
        # TODO: Replace it with something meaningful
        # for cnt, var in enumerate(self._symbols.values()):
        #     print(f'var {var.name} as Symbol with id {cnt}')
        #     interpreter.symbol(cnt)

        # for cnt, var in enumerate(self._patterns.values()):
        #     print(f'var {var.name} as Metavariable with id {cnt}')
        #     interpreter.metavar(cnt)

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

        # TODO: Patterns and notations are searched as is. It is unclear do we need to support Blocks
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
                self._scope.add_domain_value(st.terms[1].symbol)
                return True
            else:
                return False

        def symbol_axiom(st: AxiomaticStatement) -> Metavariable | None:
            if (
                isinstance(st.terms[0], Application)
                and st.terms[0].symbol == '#Symbol'
                and isinstance(st.terms[1], Application)
                and len(st.terms[1].subterms) == 0
            ):
                self._scope.add_symbol(st.terms[1].symbol)
            else:
                return None

        def sugar_axiom(st: AxiomaticStatement) -> bool:
            if (
                isinstance(st.terms[0], Application)
                and st.terms[0].symbol == '#Notation'
                and isinstance(st.terms[1], Application)
                and len(st.terms) == 3
            ):
                symbol: str = st.terms[1].symbol
                args = st.terms[1].subterms
                scope = self._scope._reduce_to_args(args)
                notation_lambda = self._to_pattern(scope, st.terms[2])
                self._notations[symbol] = notation_lambda
                return True
            else:
                return False

        if constant_is_pattern_axiom(statement):
            return
        elif symbol_axiom(statement):
            return
        elif sugar_axiom(statement):
            return
        else:
            print(f'Unknown axiom: {repr(statement)}')
            return

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
            self._scope.add_metavariable(var)
        elif var := get_symbol(statement):
            self._scope.add_symbol(var)
        elif var := get_var(statement):
            self._scope.add_metavariable(var)
        elif var := get_element_var(statement):
            self._scope.add_element_var(var)
        elif var := get_set_var(statement):
            self._scope.add_set_var(var)
        else:
            print(f'Unknown floating statement: {repr(statement)}')

    def _add_builin_notations(self) -> None:
        self._notations['\\bot'] = lambda *args: nf.Mu(nf.SVar(0), nf.SVar(0))

    def _to_pattern(self, scope: Scope, term: Term) -> Callable:
        # TODO: Process aaplications
        # TODO: Fetch notations
        # TODO: Determine variable type
        # TODO: Use essential hypotheses to determine metaconditions
        match term:
            case Application(symbol, subterms):
                if (symbol == '\\imp'):
                    assert len(subterms) == 2
                    left_term, right_term = subterms
                    left_pattern = self._to_pattern(scope, left_term)
                    right_pattern = self._to_pattern(scope, right_term)
                    return lambda *args: nf.Implication(left_pattern(*args), right_pattern(*args))
                elif (symbol == '\\app'):
                    assert len(subterms) == 2
                    left_term, right_term = subterms
                    left_pattern = self._to_pattern(scope, left_term)
                    right_pattern = self._to_pattern(scope, right_term)
                    return lambda *args: nf.Application(left_pattern(*args), right_pattern(*args))
                elif (symbol == '\\exists'):
                    assert len(subterms) == 2
                    var_term, subpattern_term = subterms
                    var_pattern = self._to_pattern(scope, var_term)
                    subpattern_pattern = self._to_pattern(scope, subpattern_term)
                    return lambda *args: nf.Exists(var_pattern(*args), subpattern_pattern(*args))
                elif symbol in self._notations:
                    notation = self._notations[symbol]
                    converted_args = tuple(self._to_pattern(scope, arg) for arg in term.subterms)
                    return lambda *args: notation(*[arg(*args) for arg in converted_args])
                elif scope.is_symbol(symbol):
                    resolved = scope.resolve(symbol)
                    return lambda *args: resolved(*args)
                else:
                    raise NotImplementedError
            case Metavariable(name):
                resolved = scope.resolve(name)
                return lambda *args: resolved(*args)
            case _:
                raise NotImplementedError
