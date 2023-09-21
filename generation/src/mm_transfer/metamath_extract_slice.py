from __future__ import annotations

import argparse
from pathlib import Path
from typing import TYPE_CHECKING, cast

from mm_transfer.metamath.ast import (
    Application,
    AxiomaticStatement,
    Block,
    ConstantStatement,
    Database,
    DisjointStatement,
    Encoder,
    EssentialStatement,
    FloatingStatement,
    Metavariable,
    ProvableStatement,
    StructuredStatement,
    VariableStatement,
)
from mm_transfer.metamath.parser import load_database

if TYPE_CHECKING:
    from collections.abc import Iterable, Iterator
    from typing import TypeGuard

    from mm_transfer.metamath.ast import Statement, Term, Terms


def get_constants(terms: Terms) -> set[str]:
    ret: set[str] = {'(', ')', '#Variable', '#ElementVariable', '#SetVariable', '#Pattern', '#Symbol'}
    for term in terms:
        if isinstance(term, Application):
            ret = ret.union({term.symbol}, get_constants(term.subterms))
    return ret


def statements_get_constants(statements: Iterable[Statement]) -> set[str]:
    ret = set()
    for statement in statements:
        if isinstance(statement, StructuredStatement):
            ret.update(get_constants(statement.terms))
        elif isinstance(statement, Block):
            ret.update(statements_get_constants(statement.statements))
        elif isinstance(statement, DisjointStatement):
            continue
        else:
            raise RuntimeError('Unexpected statement type', type(statement))
    return ret


def deconstruct_compressed_proof(provable: ProvableStatement) -> tuple[tuple[str, ...], str]:
    proof = provable.proof
    assert proof, f'Proof is missing for {provable.label}'
    lemmas_begin = proof.find('(') + 1
    lemmas_end = proof.find(')', lemmas_begin)
    assert 0 <= lemmas_begin < lemmas_end, f'Can only parse compressed proofs. {provable.label}'
    return (tuple(proof[lemmas_begin:lemmas_end].split()), proof[lemmas_end + 1 :])


def supporting_database_for_provable(
    cut_antecedents: dict[str, FloatingStatement | AxiomaticStatement | Block],
    global_disjoints: set[frozenset[str]],
    syntax_deps: dict[str, tuple[str, ...]],
    provable: ProvableStatement,
    essentials: tuple[DisjointStatement | EssentialStatement, ...],
) -> Database:
    def corresponding_sugar_axiom(label: str) -> str | None:
        if not label.endswith('is-pattern'):
            return None
        sugar_label = label[0 : -len('is-pattern')] + 'is-sugar'
        if sugar_label not in cut_antecedents.keys():
            return None
        return sugar_label

    statements: list[Statement] = []
    needed_lemmas_tuple, _ = deconstruct_compressed_proof(provable)
    needed_lemmas = frozenset(needed_lemmas_tuple)
    needed_lemmas |= frozenset(filter(None, map(corresponding_sugar_axiom, needed_lemmas)))
    for lemma in needed_lemmas:
        needed_lemmas |= frozenset(syntax_deps.get(lemma, ()))

    needed_constants = set()
    needed_metavariables = set()
    for needed in (provable, *essentials, *(cut_antecedents[lemma_name] for lemma_name in needed_lemmas)):
        needed_constants.update(statements_get_constants((needed,)))
        needed_metavariables.update(needed.get_metavariables())

    statements.append(ConstantStatement(tuple(sorted(needed_constants))))
    if needed_metavariables:
        statements.append(VariableStatement(tuple(Metavariable(var) for var in sorted(needed_metavariables))))
    for pair in global_disjoints:
        if pair.issubset(needed_metavariables):
            statements.append(DisjointStatement(tuple(Metavariable(var) for var in pair)))
    for lemma_name, lemma_statement in cut_antecedents.items():
        if lemma_name in needed_lemmas or (
            isinstance(lemma_statement, FloatingStatement) and lemma_statement.metavariable in needed_metavariables
        ):
            statements.append(lemma_statement)
    statements.append(Block((*essentials, provable)))

    return Database(tuple(statements))


def match_axiom(statement: Statement) -> AxiomaticStatement | None:
    """Returns the main statement of an axiom statement or block ending with an axiom."""
    if isinstance(statement, AxiomaticStatement):
        return statement
    if isinstance(statement, Block):
        substatements = list(statement.statements)
        while substatements:
            substatement, *substatements = substatements
            if isinstance(substatement, Block):
                substatements += substatement.statements
            elif not isinstance(substatement, (DisjointStatement, EssentialStatement, AxiomaticStatement)):
                return None
        assert isinstance(substatement, AxiomaticStatement)
        return substatement
    return None


def deconstruct_provable(
    statement: ProvableStatement | Block,
) -> tuple[tuple[DisjointStatement | EssentialStatement, ...], ProvableStatement]:
    if isinstance(statement, ProvableStatement):
        return ((), statement)
    elif isinstance(statement, Block):
        assert not match_axiom(statement)
        for substatement in statement.statements[:-1]:
            assert isinstance(substatement, (DisjointStatement, EssentialStatement)), substatement
        assert isinstance(statement.statements[-1], ProvableStatement)
        return (
            cast('tuple[DisjointStatement | EssentialStatement, ...]', tuple(statement.statements[:-1])),
            statement.statements[-1],
        )


def construct_axiom(
    antecedents: tuple[DisjointStatement | EssentialStatement, ...], consequent: ProvableStatement
) -> AxiomaticStatement | Block:
    if not antecedents:
        return AxiomaticStatement(consequent.label, consequent.terms)
    return Block((*antecedents, AxiomaticStatement(consequent.label, consequent.terms)))


def slice_database(
    input_database: Database, syntax_deps: dict[str, tuple[str, ...]], include: set[str], exclude: set[str]
) -> Iterator[tuple[str, Database]]:
    """Of the top-level statements, only floating statements are mandatory hypothesis.
    They are thus order sensitive.
    """
    cut_antecedents: dict[str, FloatingStatement | AxiomaticStatement | Block] = {}
    global_disjoints: set[frozenset[str]] = set()

    for statement in input_database.statements:
        """Constants and variables can be ignored since we can deduce the set of constants from the parsed statement."""
        if isinstance(statement, (ConstantStatement, VariableStatement)):
            continue
        elif isinstance(statement, DisjointStatement):
            for var1 in statement.metavariables:
                for var2 in statement.metavariables:
                    if var1 != var2:
                        global_disjoints.add(frozenset({var1.name, var2.name}))
        elif isinstance(statement, FloatingStatement):
            cut_antecedents[statement.label] = statement
        elif axiom_conclusion := match_axiom(statement):
            cut_antecedents[axiom_conclusion.label] = cast('AxiomaticStatement | Block', statement)
        elif isinstance(statement, (ProvableStatement, Block)):
            antecedents, consequent = deconstruct_provable(statement)
            if (consequent.label in include) and (consequent.label not in exclude):
                yield (
                    consequent.label,
                    supporting_database_for_provable(
                        cut_antecedents, global_disjoints, syntax_deps, consequent, antecedents
                    ),
                )
            cut_antecedents[consequent.label] = construct_axiom(antecedents, consequent)
        else:
            assert 'Unanticipated statement type', type(statement)


def dependency_graph(database: Database) -> dict[str, tuple[str, ...]]:
    ret = {}

    def collect(stmt: Statement) -> Statement:
        nonlocal ret
        if isinstance(stmt, ProvableStatement):
            lemmas, _ = deconstruct_compressed_proof(stmt)
            ret[stmt.label] = lemmas
        return stmt

    database.bottom_up(collect)
    return ret


def is_structured_statement(stmt: Statement) -> TypeGuard[StructuredStatement]:
    return isinstance(stmt, StructuredStatement)


def syntax_dependencies(database: Database) -> dict[str, tuple[str, ...]]:
    """Returns a maps from labels of structured statements to the
    notation and symbol axioms it depends on.
    e.g. `foo-is-sugar` and `foo-is-pattern`, and `sigma-is-symbol`
    axioms it depends on.
    """

    syntax_defs: dict[str, str] = {}
    ret: dict[str, tuple[str, ...]] = {}

    def collect_needed_syntax(term: Term) -> tuple[str, ...]:
        ret: list[str] = []

        def _collect(term: Term) -> Term:
            nonlocal ret
            if isinstance(term, Application) and term.symbol in syntax_defs:
                ret += (syntax_defs[term.symbol],)
            return term

        term.bottom_up(_collect)
        return tuple(ret)

    for stmt in database.statements:
        substmts: tuple[StructuredStatement, ...]
        if isinstance(stmt, Block):
            substmts = tuple(filter(is_structured_statement, stmt.statements))
        elif isinstance(stmt, (ProvableStatement, AxiomaticStatement)):
            substmts = (stmt,)
        else:
            continue
        conclusion = substmts[-1]

        used_notations: tuple[str, ...] = ()

        if conclusion.label.endswith('is-symbol'):
            assert len(conclusion.terms) == 2, conclusion
            sharp, symbol = conclusion.terms
            assert sharp == Application('#Symbol')
            assert isinstance(symbol, Application)
            syntax_defs[symbol.symbol] = conclusion.label
        elif conclusion.label.endswith('is-sugar'):
            assert len(conclusion.terms) == 3, conclusion
            sharp, lhs, rhs = conclusion.terms
            assert sharp == Application('#Notation')
            assert isinstance(lhs, Application)
            syntax_defs[lhs.symbol] = conclusion.label
            notation_is_pattern = conclusion.label[0 : -len('sugar')] + 'pattern'
            used_notations = used_notations + (notation_is_pattern, *collect_needed_syntax(conclusion.terms[2]))

        for substmt in substmts:
            match substmt.terms[0]:
                case Application('#Substitution'):
                    used_notations = (
                        used_notations
                        + collect_needed_syntax(substmt.terms[1])
                        + collect_needed_syntax(substmt.terms[2])
                    )
                case Application('|-'):
                    used_notations = used_notations + collect_needed_syntax(substmt.terms[1])

        syntax_deps = []
        for syntax_def in used_notations:
            syntax_deps += [syntax_def, *ret[syntax_def]]
        ret[conclusion.label] = tuple(syntax_deps)

    return ret


def transitive_closure(dependency_graph: dict[str, tuple[str, ...]], include: list[str]) -> set[str]:
    unprocessed_lemmas: list[str] = include
    ret: set[str] = set()
    while unprocessed_lemmas:
        lemma, *unprocessed_lemmas = unprocessed_lemmas
        if lemma in dependency_graph and lemma not in ret:
            unprocessed_lemmas += dependency_graph[lemma]
        ret.add(lemma)
    return ret


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument('input', help='Input Metamath database path')
    parser.add_argument('output', help='Output directory')
    args = parser.parse_args()

    print('Parsing database...', end='', flush=True)
    input_database = load_database(args.input, include_proof=True)
    print(' Done.')

    output_dir = Path(args.output)
    output_dir.mkdir()

    exclude: set[str] = set()

    print('Calculating dependency graph...', end='', flush=True)
    deps = dependency_graph(input_database)
    print(' Done.')

    print('Collecting required lemmas...', end='', flush=True)
    include: set[str] = transitive_closure(deps, ['goal'])
    print(' Done.')

    print('Calculating notation dependency graph...', end='', flush=True)
    syntax_deps = syntax_dependencies(input_database)
    print(' Done.')

    print('Writing slices...', end='', flush=True)
    for label, slice in slice_database(input_database, syntax_deps, include=include, exclude=exclude):
        with open(output_dir / (label + '.mm'), 'w') as output_file:
            Encoder.encode(output_file, slice)
    print(' Done.')


if __name__ == '__main__':
    main()
