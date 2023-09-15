from __future__ import annotations

import re
from typing import TYPE_CHECKING

from mypy_extensions import VarArg

import proof_generation.pattern as nf
from mm_transfer.converter.representation import Axiom, Notation
from mm_transfer.converter.scope import GlobalScope, to_notation_scope
from mm_transfer.metamath.ast import (
    Application,
    AxiomaticStatement,
    ConstantStatement,
    FloatingStatement,
    Metavariable,
    VariableStatement,
)
from proof_generation.proof import BasicInterpreter, StatefulInterpreter

if TYPE_CHECKING:
    from collections.abc import Callable

    from mm_transfer.converter.scope import NotationScope
    from mm_transfer.metamath.ast import Database, Term


class MetamathConverter:
    """
    Get the parsed object and try to convert it making as few iterations as possible
    """

    def __init__(self, parsed: Database, parse_axioms: bool = True) -> None:
        self.parsed = parsed
        self._scope: GlobalScope = GlobalScope()
        self._declared_constants: set[str] = set()
        self._declared_variables: dict[str, Metavariable] = {}
        self._ignored_axioms: list[AxiomaticStatement] = []
        self._axioms: dict[str, list[Axiom]] = {}
        # TODO: Remove it after we start supporting all possible axioms in all our slices
        self._convert_axioms = parse_axioms

        # Add special cases that formalized in the new format differently
        self._add_builtin_notations()

        # Go over all statements 1 by 1
        self._top_down()

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
            self._scope.add_variable(var)
        elif var := get_element_var(statement):
            self._scope.add_element_var(var)
        elif var := get_set_var(statement):
            self._scope.add_set_var(var)
        else:
            print(f'Unknown floating statement: {repr(statement)}')

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

        def symbol_axiom(st: AxiomaticStatement) -> bool:
            if (
                isinstance(st.terms[0], Application)
                and st.terms[0].symbol == '#Symbol'
                and isinstance(st.terms[1], Application)
                and len(st.terms[1].subterms) == 0
            ):
                self._scope.add_symbol(st.terms[1].symbol)
                return True
            else:
                return False

        def proved_axiom(st: AxiomaticStatement) -> bool:
            if isinstance(st.terms[0], Application) and st.terms[0].symbol == '|-':
                # TODO: Remove me later
                if self._convert_axioms:
                    self._convert_axiom(st.label, st.terms[1])
                return True
            else:
                return False

        def sugar_axiom(st: AxiomaticStatement) -> bool:
            if (
                isinstance(st.terms[0], Application)
                and st.terms[0].symbol == '#Notation'
                and isinstance(st.terms[1], Application)
                and len(st.terms) == 3
            ):
                symbol: str = st.terms[1].symbol
                args = st.terms[1].subterms

                # Typechecker cannot swallow code below, so we need to silence a warning for this assignment
                assert all(isinstance(arg, Metavariable) for arg in args)
                metavar_args: tuple[Metavariable, ...] = tuple(args)  # type: ignore
                arg_names = tuple(arg.name for arg in metavar_args)
                ambiguous_args = tuple(arg.name for arg in metavar_args if self._scope.is_ambiguous(arg))

                if len(ambiguous_args) > 0:
                    scopes = self._scope.unambiguize(ambiguous_args)
                    for scope in scopes:
                        notation_scope = to_notation_scope(scope, metavar_args)
                        notation_lambda = self._to_pattern(notation_scope, st.terms[2])
                        notation = Notation(symbol, arg_names, notation_scope.arguments_type_check, notation_lambda)
                        self._scope.add_notation(notation)
                else:
                    notation_scope = to_notation_scope(self._scope, metavar_args)
                    notation_lambda = self._to_pattern(notation_scope, st.terms[2])
                    notation = Notation(symbol, arg_names, notation_scope.arguments_type_check, notation_lambda)
                    self._scope.add_notation(notation)
                return True
            else:
                return False

        def the_rest_axioms(st: AxiomaticStatement) -> bool:
            if isinstance(st.terms[0], Application) and st.terms[0].symbol.startswith('#'):
                self._ignored_axioms.append(st)
                return True
            else:
                return False

        # $a #Pattern ...
        if constant_is_pattern_axiom(statement):
            return
        # $a #Symbol ...
        elif symbol_axiom(statement):
            return
        # $a #Notation ...
        elif sugar_axiom(statement):
            return
        elif proved_axiom(statement):
            return
        # like $a #something ...
        elif the_rest_axioms(statement):
            return
        else:
            raise NotImplementedError(f'Unknown axiom: {repr(statement)}')

    def _add_builtin_notations(self) -> None:
        bot = Notation('\\bot', (), lambda *args: True, lambda *args: nf.Mu(nf.SVar(0), nf.SVar(0)))
        self._scope.add_notation(bot)

    def _to_pattern(self, scope: NotationScope, term: Term) -> Callable[[VarArg(nf.Pattern)], nf.Pattern]:
        match term:
            case Application(symbol, subterms):
                if symbol == '\\imp':
                    assert len(subterms) == 2
                    left_term, right_term = subterms
                    left_pattern = self._to_pattern(scope, left_term)
                    right_pattern = self._to_pattern(scope, right_term)
                    return lambda *args: nf.Implication(left_pattern(*args), right_pattern(*args))
                elif symbol == '\\app':
                    assert len(subterms) == 2
                    left_term, right_term = subterms
                    left_pattern = self._to_pattern(scope, left_term)
                    right_pattern = self._to_pattern(scope, right_term)
                    return lambda *args: nf.Application(left_pattern(*args), right_pattern(*args))
                elif symbol == '\\exists':
                    assert len(subterms) == 2
                    var_term, subpattern_term = subterms
                    var_pattern = self._to_pattern(scope, var_term)
                    subpattern_pattern = self._to_pattern(scope, subpattern_term)

                    def exists(*args: nf.Pattern) -> nf.Pattern:
                        evar = var_pattern(*args)
                        assert isinstance(evar, nf.EVar)
                        return nf.Exists(evar, subpattern_pattern(*args))

                    return exists
                elif scope.is_notation(symbol):
                    converted_args = tuple(self._to_pattern(scope, arg) for arg in term.subterms)

                    def resolve_notation(*args: nf.Pattern) -> nf.Pattern:
                        real_args = [arg(*args) for arg in converted_args]
                        notation = scope.resolve_notation(symbol, *real_args)
                        return notation(*real_args)

                    return resolve_notation
                elif scope.is_symbol(symbol):
                    resolved = scope.resolve_as_callable(symbol)
                    return lambda *args: resolved(*args)
                else:
                    raise NotImplementedError
            case Metavariable(name):
                resolved = scope.resolve_as_callable(name)
                return lambda *args: resolved(*args)
            case _:
                raise NotImplementedError

    def _collect_variables(self, term: Term) -> tuple[Metavariable, ...]:
        collected_variables: list[Metavariable] = []

        todo = [term]
        while todo:
            current = todo.pop()
            if isinstance(current, Application):
                todo.extend(current.subterms)
            elif isinstance(current, Metavariable):
                if current not in collected_variables:
                    collected_variables.append(current)
            else:
                raise NotImplementedError

        return tuple(collected_variables)

    def _add_axiom(self, name: str, axiom: Axiom) -> None:
        if name in self._axioms:
            self._axioms[name].append(axiom)
        else:
            self._axioms[name] = [axiom]

    def _convert_axiom(self, name: str, term: Term) -> None:
        variables = self._collect_variables(term)
        var_names = tuple(var.name for var in variables)

        def add_axiom_for_scope(sc: NotationScope) -> None:
            notation_lambda = self._to_pattern(sc, term)
            notation = Notation(name, var_names, sc.arguments_type_check, notation_lambda)
            axiom_pattern = sc.notation_as_axiom(notation)
            axiom = Axiom(name, var_names, sc.arguments_type_check, axiom_pattern)
            self._add_axiom(name, axiom)

        if any(self._scope.is_ambiguous(var) for var in variables):
            scopes = self._scope.unambiguize(var_names)
            for scope in scopes:
                notation_scope = to_notation_scope(scope, variables)
                add_axiom_for_scope(notation_scope)
        else:
            notation_scope = to_notation_scope(self._scope, variables)
            add_axiom_for_scope(notation_scope)

    def get_all_axioms(self) -> List[Axiom]:
        axioms = []
        for axiom_list in self._axioms.values():
            axioms.extend(axiom_list)
        return axioms

    def interpret_axioms(self, interpreter: BasicInterpreter) -> None:
        axioms = self.get_all_axioms()
        for axiom in axioms:
            interpreter.publish_axiom(interpreter.pattern(axiom.pattern))
        return
