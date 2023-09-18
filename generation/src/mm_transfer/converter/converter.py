from __future__ import annotations

import re
from enum import Enum
from typing import TYPE_CHECKING

from mypy_extensions import VarArg

import proof_generation.pattern as nf
from mm_transfer.converter.representation import Axiom, ComplexAxiom, Notation
from mm_transfer.converter.scope import GlobalScope, Scope, to_notation_scope
from mm_transfer.metamath.ast import (
    Application,
    AxiomaticStatement,
    Block,
    ConstantStatement,
    DisjointStatement,
    EssentialStatement,
    FloatingStatement,
    Metavariable,
    ProvableStatement,
    Term,
    VariableStatement,
)

if TYPE_CHECKING:
    from collections.abc import Callable

    from mm_transfer.converter.scope import NotationScope
    from mm_transfer.metamath.ast import Database


class AxiomType(Enum):
    Trivial = 1
    Notation = 2
    Provable = 3
    LocalNotation = 4
    Metacondition = 5
    Substitution = 6


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
        self._declared_proof: list[int] = []

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
                    self._import_provable(last_statment)
                else:
                    raise NotImplementedError(f'Unknown statement: {repr(statement)}')
            else:
                raise NotImplementedError(f'Unknown statement: {repr(statement)}')

    def _import_provable(self, statement: ProvableStatement) -> None:
        def split_proof(proof: str) -> tuple[dict[str, int], str]:
            offset = len(statement.get_metavariables())
            lemma_n = offset + 1
            declared_lemmas: dict[str, int] = {}
            instructions: str = ""

            # TODO: Make some better whitespace handling
            for (i, letter) in enumerate(proof):
                if letter == "(":
                    break

            for (j, letter) in enumerate(proof[i+1:]):
                if letter != " ":
                    break

            buffer = ""
            for (l, letter) in enumerate(proof[i+j+1:]):
                if letter == " ":
                    declared_lemmas[lemma_n] = buffer
                    lemma_n += 1
                    buffer = ""
                    continue

                if letter == ")":
                    break

                buffer += letter

            for letter in proof[i+j+l+2:]:
                if letter == " ":
                    continue
                instructions += letter

            return (declared_lemmas, instructions)

        declared_lemmas, instructions = split_proof(statement.proof)

        #print(declared_lemmas)

        letter_to_number = {
            'A': 1, 'B': 2, 'C': 3, 'D': 4, 'E': 5, 'F': 6, 'G': 7, 'H': 8, 'I': 9,
            'J': 10, 'K': 11, 'L': 12, 'M': 13, 'N': 14, 'O': 15, 'P': 16, 'Q': 17,
            'R': 18, 'S': 19, 'T': 20
        }

        def convert_to_number(word: str) -> int:
            encoding = reversed(word)
            first_letter, *encoding = encoding

            n: int = letter_to_number[first_letter]

            letter_to_number2 = {
                'U': 1, 'V': 2, 'W': 3, 'X': 4, 'Y': 5
            }

            base = 0
            for letter in encoding:
                n += letter_to_number2[letter] * pow(5, base) * 20
                base += 1

            return n

        def convert_number_to_instr(number: int) -> str:
            if number in declared_lemmas:
                return declared_lemmas[number]

            return "Metavar|Load"


        buffer: str = ""
        for letter in instructions:
            buffer += letter
            if letter in letter_to_number:
                self._declared_proof.append(convert_number_to_instr(convert_to_number(buffer)))
                buffer = ""
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

    def _import_axiom(self, statement: AxiomaticStatement | Block) -> None:
        actual_statement = statement if isinstance(statement, AxiomaticStatement) else statement.statements[-1]
        assert isinstance(actual_statement, AxiomaticStatement)

        axiom_type = self._check_axiom(self._scope, actual_statement)
        if axiom_type == AxiomType.Trivial:
            # We are done
            return

        if not self._convert_axioms and axiom_type == AxiomType.Provable:
            # TODO: Bypass parsing for some slices
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
            scopes = (scope,)

        # Then add actual axioms or notations
        for scope in scopes:
            # Update the scope depending on the Block statements
            antecedents: tuple[nf.Pattern, ...] = ()
            if isinstance(statement, Block):
                antecedents = self._prepare_scope_for_block(statement, scope)

            if axiom_type == AxiomType.Provable:
                axiom = self._convert_axiom_for_scope(scope, actual_statement)
                if len(antecedents) > 0:
                    axiom = ComplexAxiom(axiom.name, axiom.args, axiom.type_check, axiom.pattern, antecedents)
                self._add_axiom(axiom.name, axiom)
            else:
                self._add_notation(scope, self._scope, actual_statement)

    def _check_axiom(self, scope: Scope, statement: AxiomaticStatement | EssentialStatement) -> AxiomType:
        is_constant = re.compile(r'"\S+"')

        # TODO: Patterns and notations are searched as is. It is unclear do we need to support Blocks
        def constant_is_pattern_axiom() -> bool:
            if (
                isinstance(statement.terms[0], Application)
                and statement.terms[0].symbol == '#Pattern'
                and isinstance(statement.terms[1], Application)
                and statement.terms[1].symbol in self._declared_constants
                and is_constant.match(statement.terms[1].symbol)
            ):
                # We can distinguish domain values from other constants, but we decided
                # to keep quotes in favor of the direct correspondence between Metamath
                # and the new format.
                scope.add_domain_value(statement.terms[1].symbol)
                return True
            else:
                return False

        def symbol_axiom() -> bool:
            if (
                isinstance(statement.terms[0], Application)
                and statement.terms[0].symbol == '#Symbol'
                and isinstance(statement.terms[1], Application)
                and len(statement.terms[1].subterms) == 0
            ):
                scope.add_symbol(statement.terms[1].symbol)
                return True
            else:
                return False

        def proved_axiom() -> bool:
            if isinstance(statement.terms[0], Application) and statement.terms[0].symbol == '|-':
                return True
            else:
                return False

        def sugar_axiom() -> bool:
            if (
                isinstance(statement.terms[0], Application)
                and statement.terms[0].symbol == '#Notation'
                and isinstance(statement.terms[1], Application)
                and len(statement.terms) == 3
                and (
                    statement.terms[1].symbol != statement.terms[2].symbol
                    if isinstance(statement.terms[2], Application)
                    else True
                )
            ):
                return True
            else:
                return False

        def local_notation() -> bool:
            if (
                isinstance(statement, EssentialStatement)
                and isinstance(statement.terms[0], Application)
                and statement.terms[0].symbol == '#Notation'
                and isinstance(statement.terms[1], Metavariable)
            ):
                return True
            else:
                return False

        def substitution() -> bool:
            if (
                isinstance(statement, EssentialStatement)
                and isinstance(statement.terms[0], Application)
                and statement.terms[0].symbol == '#Substitution'
            ):
                return True
            else:
                return False

        def metacondition() -> bool:
            if (
                isinstance(statement, EssentialStatement)
                and isinstance(statement.terms[0], Application)
                and statement.terms[0].symbol
                in ('#Fresh', '#ApplicationContext')  # We will add #Negative, #Positive as we add support for them
            ):
                return True
            else:
                return False

        def the_rest_axioms() -> bool:
            if (
                isinstance(statement, AxiomaticStatement)
                and isinstance(statement.terms[0], Application)
                and statement.terms[0].symbol.startswith('#')
            ):
                self._ignored_axioms.append(statement)
                return True
            else:
                return False

        # $a #Pattern ...
        if constant_is_pattern_axiom():
            return AxiomType.Trivial
        # $a #Symbol ...
        elif symbol_axiom():
            return AxiomType.Trivial
        # $a #Notation ...
        elif sugar_axiom():
            return AxiomType.Notation
        # $a |- ...
        elif proved_axiom():
            return AxiomType.Provable
        # like $a #something ...
        elif local_notation():
            return AxiomType.LocalNotation
        # $a #Substitution ...
        elif substitution():
            return AxiomType.Substitution
        # $a #Fresh ... or $d x y
        elif metacondition():
            return AxiomType.Metacondition
        # The rest we ignoring
        elif the_rest_axioms():
            return AxiomType.Trivial
        else:
            raise NotImplementedError(f'Unknown axiom: {repr(statement)}')

    def _to_pattern(self, scope: NotationScope, term: Term) -> Callable[[VarArg(nf.Pattern)], nf.Pattern]:
        def resolve_as_notation(name: str, subterms: tuple[Term, ...]) -> Callable[[VarArg(nf.Pattern)], nf.Pattern]:
            converted_args = tuple(self._to_pattern(scope, arg) for arg in subterms)

            def resolve_notation(*args: nf.Pattern) -> nf.Pattern:
                real_args = [arg(*args) for arg in converted_args]
                notation = scope.resolve_notation(name, *real_args)
                return notation(*real_args)

            return resolve_notation

        match term:
            case Application(symbol, subterms):
                if scope.is_notation(symbol):
                    return resolve_as_notation(symbol, subterms)
                elif scope.is_symbol(symbol):
                    resolved = scope.resolve_as_callable(symbol)
                    return lambda *args: resolved(*args)
                else:
                    raise NotImplementedError
            case Metavariable(name):
                if scope.is_notation(name):
                    # Assumption: local notations don't have arguments
                    subterms = ()
                    return resolve_as_notation(name, subterms)
                resolved = scope.resolve_as_callable(name)
                return lambda *args: resolved(*args)
            case _:
                raise NotImplementedError

    def _add_notation(self, scope: Scope, add_to: Scope, statement: AxiomaticStatement | EssentialStatement) -> None:
        if isinstance(statement.terms[1], Application):
            symbol: str = statement.terms[1].symbol
            args = statement.terms[1].subterms
            term = statement.terms[2]
        elif isinstance(statement.terms[1], Metavariable):
            symbol = statement.terms[1].name
            args = ()
            term = statement.terms[2]
        else:
            raise NotImplementedError

        # Typechecker cannot swallow code below, so we need to silence a warning for this assignment
        assert all(isinstance(arg, Metavariable) for arg in args)
        metavar_args: tuple[Metavariable, ...] = tuple(args)  # type: ignore
        arg_names = tuple(arg.name for arg in metavar_args)
        notation_scope = to_notation_scope(scope, metavar_args)
        notation_lambda = self._to_pattern(notation_scope, term)
        notation = Notation(symbol, arg_names, notation_scope.arguments_type_check, notation_lambda)
        add_to.add_notation(notation)

    def _add_builtin_notations(self) -> None:
        application = Notation(
            '\\app',
            ('ph0', 'ph1'),
            lambda *args: isinstance(args[0], nf.Pattern) and isinstance(args[1], nf.Pattern),
            lambda *args: nf.Application(args[0], args[1]),
        )
        self._scope.add_notation(application)
        imp = Notation(
            '\\imp',
            ('ph0', 'ph1'),
            lambda *args: isinstance(args[0], nf.Pattern) and isinstance(args[1], nf.Pattern),
            lambda *args: nf.Implication(args[0], args[1]),
        )
        self._scope.add_notation(imp)
        exists = Notation(
            '\\exists',
            ('x', 'ph1'),
            lambda *args: isinstance(args[0], nf.EVar) and isinstance(args[0], nf.Pattern),
            lambda *args: nf.Exists(args[0], args[1]),
        )
        self._scope.add_notation(exists)
        bot = Notation('\\bot', (), lambda *args: True, lambda *args: nf.Mu(nf.SVar(0), nf.SVar(0)))
        self._scope.add_notation(bot)

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

    def _get_axiom_name(self, statement: AxiomaticStatement | EssentialStatement | Block) -> str:
        if isinstance(statement, Block):
            st = statement.statements[-1]
        else:
            st = statement
        assert isinstance(st, AxiomaticStatement | EssentialStatement)
        return st.label

    def _get_axiom_term(self, statement: AxiomaticStatement | EssentialStatement | Block) -> Term:
        if isinstance(statement, Block):
            st = statement.statements[-1]
        else:
            st = statement
        assert isinstance(st, AxiomaticStatement | EssentialStatement)
        return st.terms[1]

    def _prepare_scope_for_block(self, block: Block, scope: Scope) -> tuple[nf.Pattern, ...]:
        def new_metavariable(
            metavar: nf.MetaVar,
            e_fresh: tuple[nf.EVar, ...] = (),
            s_fresh: tuple[nf.SVar, ...] = (),
            positive: tuple[nf.SVar, ...] = (),
            negative: tuple[nf.SVar, ...] = (),
            app_ctx_holes: tuple[nf.EVar, ...] = (),
        ) -> nf.MetaVar:
            name = metavar.name
            e_fresh = metavar.e_fresh + e_fresh
            s_fresh = metavar.s_fresh + s_fresh
            positive = metavar.positive + positive
            negative = metavar.negative + negative
            app_ctx_holes = metavar.app_ctx_holes + app_ctx_holes
            return nf.MetaVar(name, e_fresh, s_fresh, positive, negative, app_ctx_holes)

        def add_fresh_mc(metavar_name: str, var_name: str) -> None:
            var = scope.resolve(var_name)
            metavar = scope.resolve(metavar_name)
            assert isinstance(metavar, nf.MetaVar)
            if isinstance(var, nf.EVar):
                new_var = new_metavariable(metavar, e_fresh=(var,))
            elif isinstance(var, nf.SVar):
                new_var = new_metavariable(metavar, s_fresh=(var,))
            else:
                raise NotImplementedError
            scope.supercede_metavariable(metavar_name, new_var)

        antecedents: list[nf.Pattern] = []
        for phase in ('metaconditions', 'antecedents'):
            for statement in block.statements[:-1]:
                if phase == 'metaconditions':
                    if isinstance(statement, EssentialStatement):
                        kind = self._check_axiom(scope, statement)
                        match kind:
                            case AxiomType.Metacondition:
                                assert isinstance(statement.terms[0], Application)
                                if statement.terms[0].symbol == '#Fresh':
                                    assert isinstance(statement.terms[1], Metavariable)
                                    assert isinstance(statement.terms[2], Metavariable)

                                    var_name = statement.terms[1].name
                                    metavar_name = statement.terms[2].name
                                    add_fresh_mc(metavar_name, var_name)
                                elif statement.terms[0].symbol == '#ApplicationContext':
                                    assert isinstance(statement.terms[1], Metavariable)
                                    assert isinstance(statement.terms[2], Metavariable)

                                    var_name = statement.terms[1].name
                                    metavar_name = statement.terms[2].name
                                    var = scope.resolve(var_name)
                                    metavar = scope.resolve(metavar_name)
                                    assert isinstance(metavar, nf.MetaVar)
                                    assert isinstance(var, nf.EVar)
                                    new_var = new_metavariable(metavar, app_ctx_holes=(var,))
                                    scope.supercede_metavariable(metavar_name, new_var)
                                else:
                                    raise NotImplementedError
                            case _:
                                continue
                    elif isinstance(statement, DisjointStatement):
                        var_name = statement.metavariables[0].name
                        metavar_name = statement.metavariables[1].name
                        assert len(statement.metavariables) == 2
                        add_fresh_mc(metavar_name, var_name)
                    else:
                        raise NotImplementedError
                elif phase == 'antecedents':
                    if isinstance(statement, EssentialStatement):
                        kind = self._check_axiom(scope, statement)
                        match kind:
                            case AxiomType.LocalNotation:
                                # This notation actually replaces an existing variable
                                self._add_notation(scope, scope, statement)
                            case AxiomType.Provable:
                                axiom = self._convert_axiom_for_scope(scope, statement)
                                antecedents.append(axiom.pattern)
                            case AxiomType.Substitution:
                                # $e #Substitution ph1 ph2 ph3 xX`,
                                # we must replace `ph1` with `XSubst(ph2, ph3, xX)`
                                assert isinstance(statement.terms[1], Metavariable)
                                assert all(isinstance(arg, Term) for arg in statement.terms[2:])

                                symbol = statement.terms[1].name
                                # Typecheck is added with the 'all' statement
                                args: tuple[Metavariable, ...] = statement.terms[2:]  # type: ignore
                                assert len(args) == 3
                                notation_scope = to_notation_scope(scope, ())
                                last_arg = args[-1]
                                assert isinstance(last_arg, Metavariable)

                                def get_subst_lambda(
                                    notation_scope: NotationScope, meta_args: tuple[Metavariable, ...]
                                ) -> Callable[[VarArg(nf.Pattern)], nf.Pattern]:
                                    converted_args = tuple(self._to_pattern(notation_scope, arg) for arg in meta_args)

                                    def notation_lambda(*fargs: nf.Pattern) -> nf.Pattern:
                                        assert len(converted_args) == 3
                                        pattern, plug, var = tuple(arg(*fargs) for arg in converted_args)
                                        assert isinstance(pattern, nf.MetaVar | nf.ESubst | nf.SSubst)
                                        assert isinstance(plug, nf.Pattern)
                                        assert isinstance(var, nf.EVar | nf.SVar)
                                        if isinstance(var, nf.EVar):
                                            return nf.ESubst(pattern, var, plug)
                                        elif isinstance(var, nf.SVar):
                                            return nf.SSubst(pattern, var, plug)
                                        else:
                                            raise NotImplementedError

                                    return notation_lambda

                                notation = Notation(
                                    symbol,
                                    (),
                                    notation_scope.arguments_type_check,
                                    get_subst_lambda(notation_scope, args),
                                )
                                scope.add_notation(notation)
                            case _:
                                continue
                    else:
                        continue
                else:
                    raise NotImplementedError
        return tuple(antecedents)

    def _convert_axiom_for_scope(self, scope: Scope, statement: AxiomaticStatement | EssentialStatement) -> Axiom:
        name = self._get_axiom_name(statement)
        variables: tuple[Metavariable, ...] = self._collect_variables(statement.terms[1])
        term = self._get_axiom_term(statement)

        var_names = tuple(var.name for var in variables)
        notation_scope = to_notation_scope(scope, variables)
        notation_lambda = self._to_pattern(notation_scope, term)
        notation = Notation(name, var_names, notation_scope.arguments_type_check, notation_lambda)

        axiom_pattern = scope.notation_as_axiom(notation)
        axiom = Axiom(name, var_names, notation_scope.arguments_type_check, axiom_pattern)
        return axiom
