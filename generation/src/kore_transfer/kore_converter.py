from __future__ import annotations

from collections.abc import Callable
from itertools import count

import pyk.kore.syntax as kore

import proof_generation.pattern as nf
import proof_generation.proof as proof
import proof_generation.proofs.propositional as prop

ProofMethod = Callable[[proof.ProofExp], proof.Proved]


class KoreConverter:
    CONST_SYMBOLS: tuple[type[kore.Pattern], ...] = (kore.And, kore.Top, kore.EVar)

    def __init__(self, kore_definition: kore.Definition) -> None:
        self._definition = kore_definition

        self._symbols: dict[str, nf.Symbol] = {}
        self._evars: dict[str, nf.EVar] = {}
        self._svars: dict[str, nf.SVar] = {}
        self._metavars: dict[str, nf.MetaVar] = {}
        self._notations: dict[str, type[nf.Notation]] = {}

        self._symbol_number = count(len(self.CONST_SYMBOLS))
        self._symbol_sort_number = count(len(self.CONST_SYMBOLS) + 100)

    def convert_pattern(self, pattern: kore.Pattern) -> nf.Pattern:
        """Convert the given pattern to the pattern in the new format."""
        return self._convert_pattern(pattern)

    def _convert_pattern(self, pattern: kore.Pattern) -> nf.Pattern:
        """Convert the given pattern to the pattern in the new format."""
        # TODO: Double check everything below!
        match pattern:
            case kore.Rewrites(_, left, right):
                # TODO: Sort is ignored for now.
                left_rw_pattern = self._convert_pattern(left)
                right_rw_pattern = self._convert_pattern(right)
                return nf.Implies(left_rw_pattern, right_rw_pattern)
            case kore.And(sort, left, right):
                and_symbol: nf.Symbol = self._resolve_symbol(pattern)
                sort_symbol: nf.Pattern = self._resolve_symbol(sort)
                left_and_pattern: nf.Pattern = self._convert_pattern(left)
                right_and_pattern: nf.Pattern = self._convert_pattern(right)

                return self._resolve_notation(
                    'kore-And', and_symbol, [sort_symbol, left_and_pattern, right_and_pattern]
                )
            case kore.App(symbol, sorts, args):
                symbol_pattern: nf.Symbol = self._resolve_symbol(symbol)
                args_pattern: list[nf.Pattern] = [self._convert_pattern(arg) for arg in args]
                sorts_pattern: list[nf.Pattern] = [self._resolve_symbol(sort) for sort in sorts]
                return self._resolve_notation(symbol, symbol_pattern, [*sorts_pattern, *args_pattern])
            case kore.EVar(name, _):
                # TODO: Revisit when we have sorting implemented!
                # return self._resolve_evar(pattern)
                return self._resolve_metavar(name)
            case kore.Top(sort):
                # TODO: Revisit when we have sorting implemented!
                return prop.Top()
            case kore.DV(_, value):
                # TODO: Revisit when we have sorting implemented!
                return self._resolve_symbol(value.value)

        raise NotImplementedError(f'Pattern {pattern} is not supported')

    def _resolve_symbol(self, pattern: kore.Pattern | kore.Sort | str) -> nf.Symbol:
        """Resolve the symbol in the given pattern."""
        if isinstance(pattern, str):
            if pattern not in self._symbols:
                self._symbols[pattern] = nf.Symbol(name=next(self._symbol_number), pretty_name=pattern)
            return self._symbols[pattern]
        elif isinstance(pattern, kore.Sort):
            if pattern.name not in self._symbols:
                self._symbols[pattern.name] = nf.Symbol(name=next(self._symbol_sort_number), pretty_name=pattern.name)
            return self._symbols[pattern.name]
        elif type(pattern) in self.CONST_SYMBOLS:
            return nf.Symbol(name=self.CONST_SYMBOLS.index(type(pattern)), pretty_name=f'KORE_{type(pattern).__name__}')
        else:
            raise NotImplementedError(f'Pattern {pattern} is not supported')

    def _resolve_notation(self, name: str, symbol: nf.Symbol, arguments: list[nf.Pattern]) -> nf.Pattern:
        """Resolve the notation or make up one."""
        if name in self._notations:
            return self._notations[name](*arguments)
        else:
            return nf.FakeNotation(symbol, tuple(arguments))

    def _resolve_evar(self, evar: kore.EVar) -> nf.EVar:
        """Resolve the evar in the given pattern."""
        if evar.name not in self._evars:
            self._evars[evar.name] = nf.EVar(name=len(self._evars))
        return self._evars[evar.name]

    def _resolve_metavar(self, name: str) -> nf.MetaVar:
        """Resolve the metavar in the given pattern."""
        if name not in self._metavars:
            self._metavars[name] = nf.MetaVar(name=len(self._metavars))
        return self._metavars[name]
