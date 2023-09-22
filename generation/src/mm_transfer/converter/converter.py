from __future__ import annotations

import re
from enum import Enum
from typing import TYPE_CHECKING

from mypy_extensions import VarArg

import proof_generation.pattern as nf
from mm_transfer.converter.representation import (
    Axiom,
    AxiomWithAntecedents,
    Lemma,
    LemmaWithAntecedents,
    Notation,
    Proof,
)
from mm_transfer.converter.scope import GlobalScope, Scope, to_notation_scope
from mm_transfer.converter.vardict import VarDict
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
    from proof_generation.proof import BasicInterpreter


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
        # TODO: Remove it after we start supporting all possible axioms in all our slices
        self._convert_axioms = parse_axioms

        self._scope: GlobalScope = GlobalScope()
        self._declared_constants: set[str] = set()
        self._declared_variables: dict[str, Metavariable] = {}
        self._symbols: VarDict = VarDict(None, nf.Symbol)
        self._domain_values: set[str] = set()
        self._axioms: dict[str, list[Axiom]] = {}
        self._pattern_constructors: set[str] = set()
        self._proof_rules: set[str] = set()
        self._ignored_axioms: list[AxiomaticStatement] = []
        self._lemmas: dict[str, list[Lemma]] = {}
        self._ignored_lemmas: list[ProvableStatement] = []
        self._missing_declarations: set[str] = set()
        self._floating_patterns: list[str] = []
        self._fp_label_to_metavar: dict[str, str] = {}

        # Add special cases that formalized in the new format differently
        self._add_builtin_notations()

        # Go over all statements 1 by 1
        self._top_down()

    @property
    def lemmas(self) -> tuple[str, ...]:
        return tuple(self._lemmas.keys())

    @property
    def axioms(self) -> tuple[str, ...]:
        return tuple(self._axioms.keys())

    @property
    def exported_axioms(self) -> tuple[str, ...]:
        return tuple(axiom for axiom in self.axioms if self.is_exported_axiom(axiom))

    @property
    def exported_axioms_as_objects(self) -> tuple[Axiom, ...]:
        return tuple(axiom for name in self.exported_axioms for axiom in self._axioms[name])

    @property
    def proof_rules(self) -> set[str]:
        return set(self._proof_rules)

    @property
    def pattern_constructors(self) -> set[str]:
        return set(self._pattern_constructors)

    @property
    def missing_notations(self) -> set[str]:
        return set(self._missing_declarations)

    def is_lemma(self, name: str) -> bool:
        return name in self._lemmas

    def is_axiom(self, name: str) -> bool:
        return name in self._axioms

    def is_pattern_constructor(self, name: str) -> bool:
        return name in self._pattern_constructors

    def is_proof_rule(self, name: str) -> bool:
        return name in self._proof_rules

    def is_exported_axiom(self, name: str) -> bool:
        return self.is_axiom(name) and not self.is_pattern_constructor(name) and not self.is_proof_rule(name)

    def get_axiom_by_name(self, name: str) -> Axiom:
        # todo: Duplication is intentionally unsupported
        assert self.is_axiom(name)
        return self._axioms[name][0]

    def get_lemma_by_name(self, name: str) -> Lemma:
        # todo: Duplication is intentionally unsupported
        assert self.is_lemma(name)
        return self._lemmas[name][0]

    def publish_axioms(self, interpreter: BasicInterpreter) -> None:
        for axiom in self.exported_axioms_as_objects:
            interpreter.publish_axiom(interpreter.pattern(axiom.pattern))

    def publish_lemmas(self, interpreter: BasicInterpreter) -> None:
        raise NotImplementedError

    def get_metavars_in_order(self, name: str) -> tuple[str, ...]:
        metavars = self.get_metavars(name)
        # Now return these names in an order how they follow in self._floating_patterns
        return tuple(metavar for metavar in self._floating_patterns if metavar in metavars)

    def get_metavars(self, name: str) -> set[str]:
        if name in self._axioms:
            axiom = self._axioms[name][0]
        elif name in self._lemmas:
            axiom = self._lemmas[name][0]
        else:
            raise KeyError(f'Unknown axiom or lemma: {name}')
        assert isinstance(axiom, Axiom)
        metavars = axiom.metavars
        return set(metavars)

    def resolve_metavar(self, name: str) -> nf.MetaVar:
        assert self._scope.is_metavar(name)
        res = self._scope.resolve(name)
        assert isinstance(res, nf.MetaVar)
        return res

    def get_metavar_name_by_label(self, label: str) -> str:
        assert label in self._fp_label_to_metavar, f'Unknown floating pattern label: {label}'
        return self._fp_label_to_metavar[label]

    def _add_symbol(self, var: Metavariable | str) -> None:
        if var not in self._symbols:
            self._symbols[var] = nf.Symbol(len(self._symbols))

    def _is_symbol(self, name: str) -> bool:
        return name in self._symbols

    def _top_down(self) -> None:
        """
        Convert the database from top to bottom
        """
        notations: list[AxiomaticStatement] = []
        axioms: list[AxiomaticStatement | Block] = []
        lemmas: list[ProvableStatement | Block] = []

        def sort_axiom(statement: AxiomaticStatement, add_statement: AxiomaticStatement | Block) -> None:
            axiom_type = self._check_axiom(self._scope, statement)
            if axiom_type == AxiomType.Notation:
                notations.append(statement)
            elif axiom_type == AxiomType.Provable:
                axioms.append(add_statement)
            else:
                return

        for statement in self.parsed.statements:
            if isinstance(statement, ConstantStatement):
                self._import_constants(statement)
            elif isinstance(statement, VariableStatement):
                self._import_variables(statement)
            elif isinstance(statement, FloatingStatement):
                self._import_floating(statement)
            elif isinstance(statement, AxiomaticStatement):
                sort_axiom(statement, statement)
            elif isinstance(statement, ProvableStatement):
                lemmas.append(statement)
            elif isinstance(statement, Block):
                last_statment = statement.statements[-1]
                if isinstance(last_statment, AxiomaticStatement):
                    if self._convert_axioms:
                        sort_axiom(last_statment, statement)
                elif isinstance(last_statment, ProvableStatement):
                    if self._convert_axioms:
                        lemmas.append(statement)
                else:
                    raise NotImplementedError(f'Unknown statement: {repr(statement)}')
            else:
                raise NotImplementedError(f'Unknown statement: {repr(statement)}')

        # Second sweep
        for notation in notations:
            self._import_axiom(notation)
        for axiom in axioms:
            self._import_axiom(axiom)
        for lemma in lemmas:
            self._import_lemma(lemma)

    def _import_proof(self, statement: ProvableStatement) -> Proof:
        # Least significant digits in MM encoding
        lsdigit = {
            'A': 1,
            'B': 2,
            'C': 3,
            'D': 4,
            'E': 5,
            'F': 6,
            'G': 7,
            'H': 8,
            'I': 9,
            'J': 10,
            'K': 11,
            'L': 12,
            'M': 13,
            'N': 14,
            'O': 15,
            'P': 16,
            'Q': 17,
            'R': 18,
            'S': 19,
            'T': 20,
        }
        # "More" significant digits in MM encoding
        msdigit = {'U': 1, 'V': 2, 'W': 3, 'X': 4, 'Y': 5}

        def parse_lemmas(proof: str, declared_lemmas: dict[int, str]) -> int:
            # Skip to first (
            for _i, letter in enumerate(proof):
                if letter == '(':
                    break

            # Skip to first declared lemma
            for _j, letter in enumerate(proof[_i + 1 :]):
                if not letter.isspace():
                    break

            # Register each lemma with ' ' as a divider
            buffer = ''
            lemma_n = len(declared_lemmas) + 1
            for _l, letter in enumerate(proof[_i + _j + 1 :]):
                if letter.isspace():
                    declared_lemmas[lemma_n] = buffer
                    lemma_n += 1
                    buffer = ''
                    continue

                if letter == ')':
                    break

                buffer += letter

            # Return the offset starting at the proof sequence itself
            return _i + _j + _l + 2

        def split_proof(proof: str | None) -> tuple[dict[int, str], str]:
            assert proof
            declared_lemmas: dict[int, str] = {}

            metavars_id = 1
            # TODO: Fix the order according to the one given by MM
            for metavar in statement.get_metavariables():
                declared_lemmas[metavars_id] = f'{metavar}-is-pattern'
                metavars_id += 1

            # TODO: Add Essential Hypotheses Handling

            # TODO: Make some better whitespace handling
            offset = parse_lemmas(proof, declared_lemmas)

            applied_lemmas: str = ''
            for letter in proof[offset:]:
                if letter.isspace():
                    continue
                applied_lemmas += letter

            return (declared_lemmas, applied_lemmas)

        def convert_to_number(word: str) -> int:
            encoding = list(reversed(word))
            first_letter, *encoding = encoding

            n: int = lsdigit[first_letter]

            exp = 0
            for letter in encoding:
                n += msdigit[letter] * pow(5, exp) * 20
                exp += 1

            return n

        declared_lemmas, applied_lemmas = split_proof(statement.proof)
        result = Proof(declared_lemmas, [])

        buffer: str = ''
        for letter in applied_lemmas:
            if letter == 'Z':
                assert buffer == ''
                # The choice of 0 is arbitrary to denote Load
                result.applied_lemmas.append(0)
                continue

            buffer += letter
            if letter in lsdigit:
                result.applied_lemmas.append(convert_to_number(buffer))
                buffer = ''
                continue

        return result

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
                self._fp_label_to_metavar[st.label] = st.terms[1].name
                self._floating_patterns.append(st.terms[1].name)
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
            self._add_symbol(var)
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
        if axiom_type in (AxiomType.Trivial, AxiomType.Substitution, AxiomType.Metacondition, AxiomType.LocalNotation):
            # We don't need to do anything for such top-level axioms
            return
        elif axiom_type in (AxiomType.Notation, AxiomType.Provable):
            if not self._convert_axioms and axiom_type == AxiomType.Provable:
                # TODO: Bypass parsing for some slices
                return

            # Prepare scopes if we need more than one
            args: tuple[Metavariable, ...]
            if axiom_type == AxiomType.Provable:
                args = self._collect_variables(actual_statement.terms[1])
            elif axiom_type == AxiomType.Notation:
                # It looks like #Notation (args) (replacement)
                assert len(actual_statement.terms) == 3 and isinstance(actual_statement.terms[1], Application)
                metavar_args = actual_statement.terms[1].subterms
                # Typechecker cannot swallow code below, so we need to silence a warning for this assignment
                assert all(isinstance(arg, Metavariable) for arg in metavar_args)
                args = tuple(metavar_args)  # type: ignore
            else:
                raise NotImplementedError(f'Unexpected axiom type: {axiom_type}')

            # Get all possible scopes
            scopes = self._unambiguize_scope(args)

            # Then add actual axioms or notations
            for scope in scopes:
                # Update the scope depending on the Block statements
                antecedents: tuple[Axiom, ...] = ()
                if isinstance(statement, Block):
                    antecedents = self._prepare_scope_for_block(statement, scope)

                if axiom_type == AxiomType.Provable:
                    axiom = self._convert_axiom_for_scope(scope, actual_statement)
                    if len(antecedents) > 0:
                        metavar_names = set(axiom.metavars)
                        for antecedent in antecedents:
                            metavar_names.update(antecedent.metavars)
                        axiom = AxiomWithAntecedents(
                            axiom.name,
                            axiom.args,
                            axiom.type_check,
                            axiom.pattern,
                            tuple(metavar_names),
                            tuple(a.pattern for a in antecedents),
                        )
                    self._add_axiom(axiom.name, axiom)
                else:
                    self._add_notation(scope, self._scope, actual_statement)
        else:
            raise NotImplementedError(f'Unknown axiom type: {axiom_type}')

    def _import_lemma(self, statement: ProvableStatement | Block) -> None:
        actual_statement = statement if isinstance(statement, ProvableStatement) else statement.statements[-1]
        assert isinstance(actual_statement, ProvableStatement)

        if not self._convert_axioms:
            # TODO: Remove this after we start supporting all possible axioms in all our slices
            return
        if not (isinstance(actual_statement.terms[0], Application) and actual_statement.terms[0].symbol == '|-'):
            self._ignored_lemmas.append(actual_statement)
            return

        # Prepare scopes if we need more than one
        args = self._collect_variables(actual_statement.terms[1])
        scopes = self._unambiguize_scope(args)

        # Then add actual axioms or notations
        for scope in scopes:
            # Update the scope depending on the Block statements
            antecedents: tuple[Axiom, ...] = ()
            if isinstance(statement, Block):
                antecedents = self._prepare_scope_for_block(statement, scope)

            lemma = self._convert_axiom_for_scope(scope, actual_statement)
            assert isinstance(lemma, Lemma)
            if len(antecedents) > 0:
                metavar_names = set(lemma.metavars)
                for antecedent in antecedents:
                    metavar_names.update(antecedent.metavars)
                lemma = LemmaWithAntecedents(
                    lemma.name,
                    lemma.args,
                    lemma.type_check,
                    lemma.pattern,
                    tuple(metavar_names),
                    tuple(a.pattern for a in antecedents),
                    # TODO: Add support for using antecedents
                    # self._import_proof(actual_statement)
                )
            self._add_lemma(lemma.name, lemma)

    def _check_axiom(self, scope: Scope, statement: AxiomaticStatement | EssentialStatement) -> AxiomType:
        is_constant = re.compile(r'"\S+"')

        def constant_is_pattern_axiom(st: AxiomaticStatement | EssentialStatement) -> bool:
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
                self._add_symbol(st.terms[1].symbol)
                return True
            else:
                return False

        def is_pattern_axiom(st: AxiomaticStatement | EssentialStatement) -> bool:
            if isinstance(st.terms[0], Application) and st.terms[0].symbol == '#Pattern':
                self._pattern_constructors.add(st.label)
                return True
            else:
                return False

        def symbol_axiom(st: AxiomaticStatement | EssentialStatement) -> bool:
            if (
                isinstance(st.terms[0], Application)
                and st.terms[0].symbol == '#Symbol'
                and isinstance(st.terms[1], Application)
                and len(st.terms[1].subterms) == 0
            ):
                self._add_symbol(st.terms[1].symbol)
                return True
            else:
                return False

        def proved_axiom(st: AxiomaticStatement | EssentialStatement) -> bool:
            if isinstance(st.terms[0], Application) and st.terms[0].symbol == '|-':
                if isinstance(st, AxiomaticStatement) and st.label.startswith('proof-rule-'):
                    self._proof_rules.add(st.label)
                return True
            else:
                return False

        def sugar_axiom(st: AxiomaticStatement | EssentialStatement) -> bool:
            if (
                isinstance(st.terms[0], Application)
                and st.terms[0].symbol == '#Notation'
                and isinstance(st.terms[1], Application)
                and len(st.terms) == 3
                and (st.terms[1].symbol != st.terms[2].symbol if isinstance(st.terms[2], Application) else True)
            ):
                return True
            else:
                return False

        def local_notation(st: AxiomaticStatement | EssentialStatement) -> bool:
            if (
                isinstance(st, EssentialStatement)
                and isinstance(st.terms[0], Application)
                and st.terms[0].symbol == '#Notation'
                and isinstance(st.terms[1], Metavariable)
            ):
                return True
            else:
                return False

        def substitution(st: AxiomaticStatement | EssentialStatement) -> bool:
            if (
                isinstance(st, EssentialStatement)
                and isinstance(st.terms[0], Application)
                and st.terms[0].symbol == '#Substitution'
            ):
                return True
            else:
                return False

        def metacondition(st: AxiomaticStatement | EssentialStatement) -> bool:
            if (
                isinstance(st, EssentialStatement)
                and isinstance(st.terms[0], Application)
                and st.terms[0].symbol in ('#Fresh', '#ApplicationContext', '#Positive', '#Negative')
            ):
                return True
            else:
                return False

        def the_rest_axioms(st: AxiomaticStatement | EssentialStatement) -> bool:
            if (
                isinstance(st, AxiomaticStatement)
                and isinstance(st.terms[0], Application)
                and st.terms[0].symbol.startswith('#')
            ):
                self._ignored_axioms.append(st)
                return True
            else:
                return False

        # $a #Pattern 101010
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
        # $a #Pattern ...
        elif is_pattern_axiom(statement):
            return AxiomType.Provable
        # like $a #something ...
        elif local_notation(statement):
            return AxiomType.LocalNotation
        # $a #Substitution ...
        elif substitution(statement):
            return AxiomType.Substitution
        # $a #Fresh ... or $d x y
        elif metacondition(statement):
            return AxiomType.Metacondition
        # The rest we ignoring
        elif the_rest_axioms(statement):
            return AxiomType.Trivial
        else:
            raise NotImplementedError(f'Unknown axiom: {repr(statement)}')

    def _unambiguize_scope(self, args: tuple[Metavariable, ...]) -> tuple[Scope, ...]:
        ambiguous_args = tuple(arg.name for arg in args if self._scope.is_ambiguous(arg))
        if len(ambiguous_args) > 0:
            scopes = self._scope.unambiguize(ambiguous_args)
        else:
            scope = Scope()
            scope.import_from_scope(self._scope)
            scopes = (scope,)
        return scopes

    def _to_pattern(self, scope: NotationScope, term: Term) -> Callable[[VarArg(nf.Pattern)], nf.Pattern]:
        def resolve_as_notation(name: str, subterms: tuple[Term, ...]) -> Callable[[VarArg(nf.Pattern)], nf.Pattern]:
            converted_args = tuple(self._to_pattern(scope, arg) for arg in subterms)

            def resolve_notation(*args: nf.Pattern) -> nf.Pattern:
                real_args = [arg(*args) for arg in converted_args]
                notation = scope.resolve_notation(name, *real_args)
                return notation(*real_args)

            return resolve_notation

        def resolve_as_app(
            left: Callable[[VarArg(nf.Pattern)], nf.Pattern], right: Callable[[VarArg(nf.Pattern)], nf.Pattern]
        ) -> Callable[[VarArg(nf.Pattern)], nf.Pattern]:
            app = scope.resolve_notation('\\app')

            def symbol_application(*args: nf.Pattern) -> nf.Pattern:
                real_args = (left(*args), right(*args))
                return app(*real_args)

            return symbol_application

        match term:
            case Application(symbol, subterms):
                if scope.is_notation(symbol):
                    return resolve_as_notation(symbol, subterms)
                else:
                    converted = self._resolve_as_callable(scope, symbol)
                    if symbol in self._missing_declarations and len(subterms) > 0:
                        converted_args = [self._to_pattern(scope, arg) for arg in subterms]

                        current_callable = converted
                        while len(converted_args) > 0:
                            next_one, *converted_args = converted_args
                            current_callable = resolve_as_app(current_callable, next_one)

                        return current_callable
                    else:
                        return converted
            case Metavariable(name):
                if scope.is_notation(name):
                    # Assumption: local notations don't have arguments
                    subterms = ()
                    return resolve_as_notation(name, subterms)
                else:
                    resolved = self._resolve_as_callable(scope, name)
                    return lambda *args: resolved(*args)
            case _:
                raise NotImplementedError(str(term))

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
        notation = Notation(symbol, arg_names, self._get_arguments_type_check(notation_scope), notation_lambda)
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
        self._scope.add_notation(
            Notation(
                '\\mu',
                ('X', 'ph1'),
                lambda *args: isinstance(args[0], nf.SVar) and isinstance(args[0], nf.Pattern),
                lambda *args: nf.Mu(args[0], args[1]),
            )
        )
        bot = Notation('\\bot', (), lambda *args: True, lambda *args: nf.Mu(nf.SVar(0), nf.SVar(0)))
        self._scope.add_notation(bot)
        not_ = Notation(
            '\\not',
            ('ph0',),
            lambda *args: True,
            lambda *args: nf.Implication(args[0], bot()),
        )
        self._scope.add_notation(not_)
        or_ = Notation(
            '\\or',
            ('ph0', 'ph1'),
            lambda *args: True,
            lambda *args: nf.Implication(not_(args[0]), args[1]),
        )
        self._scope.add_notation(or_)
        and_ = Notation(
            '\\and', ('ph0', 'ph1'), lambda *args: True, lambda *args: not_(or_(not_(args[0]), not_(args[1])))
        )
        self._scope.add_notation(and_)
        top = Notation('\\top', (), lambda *args: True, lambda *args: not_(bot()))
        self._scope.add_notation(top)

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

    def _add_lemma(self, name: str, lemma: Lemma) -> None:
        if name in self._lemmas:
            self._lemmas[name].append(lemma)
        else:
            self._lemmas[name] = [lemma]

    def _get_axiom_name(self, statement: AxiomaticStatement | EssentialStatement | ProvableStatement | Block) -> str:
        if isinstance(statement, Block):
            st = statement.statements[-1]
        else:
            st = statement
        assert isinstance(st, AxiomaticStatement | EssentialStatement | ProvableStatement)
        return st.label

    def _get_axiom_term(self, statement: AxiomaticStatement | EssentialStatement | ProvableStatement | Block) -> Term:
        if isinstance(statement, Block):
            st = statement.statements[-1]
        else:
            st = statement
        assert isinstance(st, AxiomaticStatement | EssentialStatement | ProvableStatement)
        return st.terms[1]

    def _prepare_scope_for_block(self, block: Block, scope: Scope) -> tuple[Axiom, ...]:
        # Typecheck for the assignments two lines below
        assert all(isinstance(st, EssentialStatement | DisjointStatement) for st in block.statements[:-1])
        eh_statements: list[EssentialStatement | DisjointStatement] = block.statements[:-1]  # type: ignore

        # Update the scope with new notations and metaconditions
        self._convert_metaconditions(
            scope,
            tuple(filter(lambda st: isinstance(st, EssentialStatement | DisjointStatement), eh_statements)),
        )

        # Now add antedecents
        only_es = tuple(filter(lambda st: isinstance(st, EssentialStatement), eh_statements))
        antecedents: tuple[Axiom, ...] = self._convert_antecedents(scope, only_es)  # type: ignore
        return antecedents

    def _convert_metaconditions(
        self, scope: Scope, statements: tuple[EssentialStatement | DisjointStatement, ...]
    ) -> None:
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

        for statement in statements:
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
                        elif statement.terms[0].symbol in ('#ApplicationContext', '#Positive', '#Negative'):
                            assert isinstance(statement.terms[1], Metavariable)
                            assert isinstance(statement.terms[2], Metavariable)

                            var_name = statement.terms[1].name
                            metavar_name = statement.terms[2].name
                            var = scope.resolve(var_name)
                            metavar = scope.resolve(metavar_name)
                            assert isinstance(metavar, nf.MetaVar)

                            if statement.terms[0].symbol == '#ApplicationContext':
                                assert isinstance(var, nf.EVar)
                                new_var = new_metavariable(metavar, app_ctx_holes=(var,))
                            elif statement.terms[0].symbol == '#Positive':
                                assert isinstance(var, nf.SVar)
                                new_var = new_metavariable(metavar, positive=(var,))
                            elif statement.terms[0].symbol == '#Negative':
                                assert isinstance(var, nf.SVar)
                                new_var = new_metavariable(metavar, negative=(var,))
                            else:
                                raise NotImplementedError(f'Unsupported symbol {statement.terms[0].symbol}')
                            scope.supercede_metavariable(metavar_name, new_var)
                        else:
                            raise NotImplementedError
                    case _:
                        continue
            elif isinstance(statement, DisjointStatement):
                assert len(statement.metavariables) == 2
                var_name = statement.metavariables[0].name
                metavar_name = statement.metavariables[1].name

                resolved_var = scope.resolve(var_name)
                assert isinstance(resolved_var, nf.EVar | nf.SVar)
                resolved_metavar = scope.resolve(metavar_name)

                if isinstance(resolved_metavar, nf.MetaVar):
                    add_fresh_mc(metavar_name, var_name)
                elif isinstance(resolved_metavar, nf.EVar | nf.SVar):
                    # We just need to check their identifier without touching the scope
                    assert resolved_metavar.name != resolved_var.name
                else:
                    raise NotImplementedError
            else:
                raise NotImplementedError

    def _convert_antecedents(self, scope: Scope, statements: tuple[EssentialStatement, ...]) -> tuple[Axiom, ...]:
        antecedents: list[Axiom] = []
        for statement in statements:
            kind = self._check_axiom(scope, statement)
            match kind:
                case AxiomType.LocalNotation:
                    # This notation actually replaces an existing variable
                    self._add_notation(scope, scope, statement)
                case AxiomType.Provable:
                    axiom = self._convert_axiom_for_scope(scope, statement)
                    antecedents.append(axiom)
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
                        self._get_arguments_type_check(notation_scope),
                        get_subst_lambda(notation_scope, args),
                    )
                    scope.add_notation(notation)
                case _:
                    continue
        return tuple(antecedents)

    def _convert_axiom_for_scope(
        self, scope: Scope, statement: AxiomaticStatement | EssentialStatement | ProvableStatement
    ) -> Axiom:
        name = self._get_axiom_name(statement)
        variables: tuple[Metavariable, ...] = self._collect_variables(statement.terms[1])
        term = self._get_axiom_term(statement)

        var_names: tuple[str, ...] = tuple(var.name for var in variables)
        metavars: tuple[str, ...] = tuple(sorted({var for var in var_names if scope.is_metavar(var)}))
        notation_scope = to_notation_scope(scope, variables)
        notation_lambda = self._to_pattern(notation_scope, term)
        notation = Notation(name, var_names, self._get_arguments_type_check(notation_scope), notation_lambda)

        args = [self._resolve(scope, arg) for arg in notation.args]
        axiom_pattern = notation(*args)
        if isinstance(statement, AxiomaticStatement | EssentialStatement):
            axiom = Axiom(name, var_names, self._get_arguments_type_check(notation_scope), axiom_pattern, metavars)
        elif isinstance(statement, ProvableStatement):
            axiom = Lemma(
                name,
                var_names,
                self._get_arguments_type_check(notation_scope),
                axiom_pattern,
                metavars,
                self._import_proof(statement),
            )
        else:
            raise NotImplementedError
        return axiom

    def _resolve(self, scope: Scope, name: str) -> nf.Pattern:
        if self._is_symbol(name):
            return self._symbols[name]
        elif name in self._declared_constants:
            # This is missing notation likely
            self._add_symbol(name)
            self._missing_declarations.add(name)
            return self._symbols[name]
        else:
            return scope.resolve(name)

    def _resolve_as_callable(
        self, notation_scope: NotationScope, name: str
    ) -> Callable[[VarArg(nf.Pattern)], nf.Pattern]:
        position = notation_scope.is_arg(name)
        if position is not None:

            def match_arg(*args: nf.Pattern) -> nf.Pattern:
                assert len(args) > position
                return args[position]

            return match_arg
        else:
            var = self._resolve(notation_scope, name)
            return lambda *args: var

    def _get_arguments_type_check(self, notation_scope: NotationScope) -> Callable[[VarArg(nf.Pattern)], bool]:
        def arguments_type_check(*args: nf.Pattern) -> bool:
            for index, name in enumerate(notation_scope.arguments):
                real_arg = args[index]
                expected_type = type(self._resolve(notation_scope, name))
                if expected_type is nf.MetaVar and isinstance(real_arg, nf.Pattern):
                    continue
                elif isinstance(real_arg, expected_type):
                    continue
                else:
                    return False
            return True

        return arguments_type_check
