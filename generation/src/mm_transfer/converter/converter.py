from __future__ import annotations

import re
from enum import Enum
from typing import TYPE_CHECKING

from mypy_extensions import VarArg

import proof_generation.pattern as nf
from mm_transfer.converter.representation import Axiom, Notation
from mm_transfer.converter.scope import GlobalScope, Scope, to_notation_scope
from mm_transfer.metamath.ast import (
    Application,
    AxiomaticStatement,
    Block,
    ConstantStatement,
    FloatingStatement,
    Metavariable,
    ProvableStatement,
    VariableStatement,
)

if TYPE_CHECKING:
    from collections.abc import Callable

    from mm_transfer.converter.scope import NotationScope
    from mm_transfer.metamath.ast import Database, Term


class AxiomType(Enum):
    Trivial = 1
    Notation = 2
    Provable = 3


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
            elif isinstance(statement, VariableStatement):
                self._import_variables(statement)
            elif isinstance(statement, FloatingStatement):
                self._import_floating(statement)
            elif isinstance(statement, AxiomaticStatement):
                self._import_axiom(statement)
            elif isinstance(statement, Block):
                last_statment = statement.statements[-1]
                if isinstance(last_statment, AxiomaticStatement):
                    # TODO: Remove me later
                    if self._convert_axioms:
                        self._import_axiom(statement)
                elif isinstance(last_statment, ProvableStatement):
                    # TODO: Implement parsing lemmas and proofs
                    pass
                else:
                    raise NotImplementedError(f'Unknown statement: {repr(statement)}')
            else:
                raise NotImplementedError(f'Unknown statement: {repr(statement)}')

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

    def _import_axiom(self, statement: AxiomaticStatement | Block) -> None:
        actual_statement = statement if isinstance(statement, AxiomaticStatement) else statement.statements[-1]
        assert isinstance(actual_statement, AxiomaticStatement)

        if isinstance(statement, Block):
            # TODO: Ignore for now
            return

        axiom_type = self._check_axiom(self._scope, actual_statement)
        if axiom_type == AxiomType.Trivial:
            # We are done
            return

        if not self._convert_axioms and axiom_type == AxiomType.Provable:
            # TODO: Ignore for now
            return

        # Prepare scopes if we need more than one
        args: tuple[Metavariable, ...] = ()
        if axiom_type == AxiomType.Provable:
            args = self._collect_variables(actual_statement.terms[1])
        else:
            assert len(actual_statement.terms) == 3 and isinstance(actual_statement.terms[1], Application)
            metavar_args = actual_statement.terms[1].subterms
            # Typechecker cannot swallow code below, so we need to silence a warning for this assignment
            assert all(isinstance(arg, Metavariable) for arg in metavar_args)
            args = tuple(metavar_args)  # type: ignore

        ambiguous_args = tuple(arg.name for arg in args if self._scope.is_ambiguous(arg))
        if len(ambiguous_args) > 0:
            scopes = self._scope.unambiguize(ambiguous_args)
        else:
            scope = Scope()
            scope.import_from_scope(self._scope)
            scopes = (self._scope,)

        # Then add actual axioms or notations
        for scope in scopes:
            # Update the scope depending on the Block statements
            self._prepare_scope_for_block(statement, scope)

            if axiom_type == AxiomType.Provable:
                self._convert_axiom_for_scope(scope, actual_statement)
            else:
                self._add_notation(scope, self._scope, actual_statement)

    def _check_axiom(self, scope: Scope, statement: AxiomaticStatement) -> AxiomType:
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
                scope.add_domain_value(st.terms[1].symbol)
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
                scope.add_symbol(st.terms[1].symbol)
                return True
            else:
                return False

        def proved_axiom(st: AxiomaticStatement) -> bool:
            if isinstance(st.terms[0], Application) and st.terms[0].symbol == '|-':
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
            return AxiomType.Trivial
        # $a #Symbol ...
        elif symbol_axiom(statement):
            return AxiomType.Trivial
        # $a #Notation ...
        elif sugar_axiom(statement):
            return AxiomType.Notation
        # $a |- ...
        elif proved_axiom(statement):
            return AxiomType.Provable
        # like $a #something ...
        elif the_rest_axioms(statement):
            return AxiomType.Trivial
        else:
            raise NotImplementedError(f'Unknown axiom: {repr(statement)}')

    def _add_notation(self, scope: Scope, add_to: Scope, statement: AxiomaticStatement) -> None:
        assert isinstance(statement.terms[1], Application)
        symbol: str = statement.terms[1].symbol
        args = statement.terms[1].subterms
        term = statement.terms[2]

        # Typechecker cannot swallow code below, so we need to silence a warning for this assignment
        assert all(isinstance(arg, Metavariable) for arg in args)
        metavar_args: tuple[Metavariable, ...] = tuple(args)  # type: ignore
        arg_names = tuple(arg.name for arg in metavar_args)
        notation_scope = to_notation_scope(scope, metavar_args)
        notation_lambda = self._to_pattern(notation_scope, term)
        notation = Notation(symbol, arg_names, notation_scope.arguments_type_check, notation_lambda)
        add_to.add_notation(notation)

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

    def _get_axiom_name(self, statement: AxiomaticStatement | Block) -> str:
        if isinstance(statement, Block):
            st = statement.statements[-1]
        else:
            st = statement
        assert isinstance(st, AxiomaticStatement)
        return st.label

    def _get_axiom_term(self, statement: AxiomaticStatement | Block) -> Term:
        if isinstance(statement, Block):
            st = statement.statements[-1]
        else:
            st = statement
        assert isinstance(st, AxiomaticStatement)
        return st.terms[1]

    def _prepare_scope_for_block(self, statement: Block | AxiomaticStatement, scope: Scope) -> None:
        # Make a new scope for the block because parent can be a global scope that we don't wanna touch
        pass

    def _convert_axiom_for_scope(self, scope: Scope, statement: AxiomaticStatement) -> None:
        name = self._get_axiom_name(statement)
        variables: tuple[Metavariable, ...] = self._collect_variables(statement.terms[1])
        term = self._get_axiom_term(statement)

        var_names = tuple(var.name for var in variables)
        notation_scope = to_notation_scope(scope, variables)
        notation_lambda = self._to_pattern(notation_scope, term)
        notation = Notation(name, var_names, notation_scope.arguments_type_check, notation_lambda)

        axiom_pattern = scope.notation_as_axiom(notation)
        axiom = Axiom(name, var_names, notation_scope.arguments_type_check, axiom_pattern)
        self._add_axiom(name, axiom)
