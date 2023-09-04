from __future__ import annotations

import os
import re
from typing import TYPE_CHECKING

from lark import Lark, Token, Transformer

from mm_transfer.metamath.ast import (
    Application,
    AxiomaticStatement,
    BaseAST,
    Block,
    ConstantStatement,
    Database,
    DisjointStatement,
    EssentialStatement,
    FloatingStatement,
    Metavariable,
    ProvableStatement,
    VariableStatement,
)

if TYPE_CHECKING:
    from collections.abc import Iterable

    from mm_transfer.metamath.ast import Statement, Term, Terms


class ASTTransformer(Transformer[Token, BaseAST]):
    def __init__(self, metavariables: Iterable[str] = ()) -> None:
        super().__init__()
        self.metavariables = list(metavariables)

    def token(self, args: list[Token]) -> str:
        assert isinstance(args[0].value, str)
        return args[0].value

    def constant_stmt(self, args: list[str]) -> ConstantStatement:
        return ConstantStatement(tuple(args))

    def variable_stmt(self, args: list[str]) -> VariableStatement:
        self.metavariables += args
        return VariableStatement(tuple(map(Metavariable, args)))

    def disjoint_stmt(self, args: list[str]) -> DisjointStatement:
        for var in args:
            assert var in self.metavariables, f'variable {var} used before declaration'
        return DisjointStatement(tuple(map(Metavariable, args)))

    def floating_stmt(self, args: list[str]) -> FloatingStatement:
        label, typecode, variable = args
        assert variable in self.metavariables, f'variable {variable} used before declaration'
        return FloatingStatement(label, (Application(typecode), Metavariable(variable)))

    def parse_term(self, tokens: list[str]) -> tuple[Term, list[str]]:
        """
        Parse a term from a list of tokens, returns the term and the rest of the unused tokens
        """
        assert len(tokens)

        first = tokens[0]
        if first == '(':
            # separate out sublist of tokens with balanced parentheses
            num_nested = 1
            for i, token in enumerate(tokens[1:]):  # noqa: B007
                if token == '(':
                    num_nested += 1
                elif token == ')':
                    num_nested -= 1
                if num_nested == 0:
                    break

            # offset to include the first token
            i += 1

            assert num_nested == 0, 'incorrectly nested term: {}'.format(' '.join(tokens))
            assert i > 2, 'ill-formed s-expression: {}'.format(' '.join(tokens))

            subterms = self.parse_terms(tokens[2:i])
            constant = tokens[1]
            return Application(constant, subterms), tokens[i + 1 :]

        elif first in self.metavariables:
            return Metavariable(first), tokens[1:]
        else:
            return Application(first), tokens[1:]

    def parse_terms(self, tokens: list[str]) -> Terms:
        terms = []
        while len(tokens):
            term, tokens = self.parse_term(tokens)
            terms.append(term)
        return tuple(terms)

    def axiom_stmt(self, args: list[str]) -> AxiomaticStatement:
        label, *tokens = args
        terms = self.parse_terms(tokens)
        return AxiomaticStatement(label, terms)

    def essential_stmt(self, args: list[str]) -> EssentialStatement:
        label, *tokens = args
        terms = self.parse_terms(tokens)
        return EssentialStatement(label, terms)

    def proof(self, args: list[str]) -> list[str]:
        return args

    def provable_stmt(self, args: list[str]) -> ProvableStatement:
        label, *args = args
        script = list(args[-1])
        tokens = args[:-1]
        terms = self.parse_terms(tokens)
        return ProvableStatement(label, terms, ' '.join(script))

    def block(self, args: list[Statement]) -> Block:
        return Block(tuple(args))

    def database(self, args: list[Statement]) -> Database:
        return Database(tuple(args))


syntax = r"""
// see http://us.metamath.org/downloads/metamath.pdf appendix E for more info
// this syntax is more relaxed than the standard syntax

COMMENT: /\$\(((.|\n)(?<!\$\)))*\$\)/

%ignore COMMENT
%ignore /[ \n\t\f\r]+/

TOKEN: /[^ \n\t\f\r\$]+/

token: TOKEN

database: stmt*

stmt: "$c" token+ "$."                   -> constant_stmt
    | "$v" token+ "$."                   -> variable_stmt
    | "$d" token+ "$."                   -> disjoint_stmt
    | token "$f" token token "$."        -> floating_stmt
    | token "$e" token+ "$."             -> essential_stmt
    | token "$a" token+ "$."             -> axiom_stmt
    | token "$p" token+ "$=" proof "$."  -> provable_stmt
    | "${" stmt* "$}"                    -> block

proof: token*
"""

database_parser = Lark(
    syntax,
    start='database',
    parser='lalr',
    lexer='basic',
    propagate_positions=True,
)

statement_parser = Lark(
    syntax,
    start='stmt',
    parser='lalr',
    lexer='basic',
    propagate_positions=True,
)


def parse_database(src: str) -> Database:
    tree = database_parser.parse(src)
    ast = ASTTransformer().transform(tree)
    assert isinstance(ast, Database)
    return ast


def parse_terms_with_metavariables(src: str, metavariables: frozenset[str] = frozenset()) -> Terms:
    tree = statement_parser.parse(f'l $a {src} $.')
    stmt = ASTTransformer(metavariables).transform(tree)
    assert isinstance(stmt, AxiomaticStatement)
    return stmt.terms


def parse_term_with_metavariables(src: str, metavariables: frozenset[str] = frozenset()) -> Term:
    terms = parse_terms_with_metavariables(src, metavariables)
    assert len(terms) == 1, f'syntax error: {src}'
    return terms[0]


def flatten_includes(path: str, loaded: set[str], trace: tuple[str, ...] = (), include_proof: bool = True) -> str:
    """
    Load a file and resolve all includes
    """
    path = os.path.realpath(path)

    if path in loaded:
        return ''

    if path in trace:
        raise Exception(f'recursivly loading {path}')

    with open(path) as mm_file:
        source = mm_file.read()

        if not include_proof:
            source = remove_proof(source)

        while True:
            match = re.search(r'\$\[\s+([^\s]+)\s+\$\]', source)
            if match is None:
                break

            include_path = match.group(1)

            # if not os.path.isabs(include_path):
            #     include_path = os.path.join(os.path.dirname(path), include_path)

            included_source = flatten_includes(include_path, loaded, trace=trace + (path,), include_proof=include_proof)
            source = source[: match.start()] + included_source + source[match.end() :]

    loaded.add(path)

    return source


def remove_proof(src: str) -> str:
    # remove comments first
    src = re.sub(r'\$\(((.|\n)(?<!\$\)))*\$\)', '', src)
    return re.sub(r'\$=\s*[^\$]*\s*\$\.', '$= ? $.', src)


def load_database(path: str, include_proof: bool = True) -> Database:
    src = flatten_includes(path, set(), include_proof=include_proof)
    return parse_database(src)
