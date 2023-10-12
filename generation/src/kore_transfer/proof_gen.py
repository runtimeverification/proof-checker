from __future__ import annotations

from typing import TYPE_CHECKING
import pyk.kore.syntax as kore
import proof_generation.pattern as nf
import proof_generation.proofs.propositional as prop

if TYPE_CHECKING:
    pass


class ExecutionProofGen():

    CONST_SYMBOLS: tuple[type[kore.Pattern], ...] = (
        kore.And,
        kore.Top,
        kore.EVar
    )

    def __init__(self, kore_definition: kore.Definition, module_name: str) -> None:
        self._definition = kore_definition
        self._module = module_name

        self._symbols: dict[str, nf.Symbol] = {}
        self._evars: dict[str, nf.EVar] = {}
        self._svars: dict[str, nf.SVar] = {}
        self._notations: dict[str, type[nf.Notation]] = {}
        self._axioms: list[nf.Pattern] = []

        # Prepare gamma phase
        # 1. Find the relevant rule and the corresponding substitution
        axioms_for_rules = self._find_rules_for_convertion()
        for axiom in axioms_for_rules:
            self._axioms.append(self._convert_axiom(axiom))

    def take_rewrite_step(self, init_config: kore.Pattern) -> None:
        """Take a single rewrite step and emit a proof for it."""
        # emit a proof for taking a single step
        # returns the final pattern
        pass

    def convert_pattern(self, pattern: kore.Pattern) -> nf.Pattern:
        """Convert the given pattern to the pattern in the new format."""
        return self._convert_pattern(pattern)

    def _find_rules_for_convertion(self) -> list[kore.Axiom]:
        """Find axioms assotiated with certain rewriting rules from the provided module."""
        # Find the _module in axioms in definition.modules and find all rules that contain kore.Rewrites
        module_axioms: list[kore.Axiom] = []
        for module in self._definition.modules:
            if module.name == self._module:
                # Select only patterns below that starts with kore.Rewrites
                module_axioms = [axiom for axiom in module.axioms if isinstance(axiom.pattern, kore.Rewrites)]
                break
        else:
            # module not found
            raise ValueError(f'Module {self._module} not found in definition')

        return module_axioms

    def _convert_axiom(self, axiom: kore.Axiom) -> nf.Pattern:
        """Convert the given axiom to the axiom in the new format."""
        new_pattern = self._convert_pattern(axiom.pattern)
        return new_pattern

    def _convert_pattern(self, pattern: kore.Pattern) -> nf.Pattern:
        """Convert the given pattern to the pattern in the new format."""
        # TODO: Double check everything below!
        match pattern:
            case kore.Rewrites(_, left, right):
                # TODO: Sort is ignored for now.
                left = self._convert_pattern(left)
                right = self._convert_pattern(right)
                return nf.Implication(left, right)
            case kore.And(sort, left, right):
                and_symbol: nf.Pattern = self._resolve_symbol(pattern)
                sort_symbol: nf.Pattern = self._resolve_symbol(sort)
                left_pattern: nf.Pattern = self._convert_pattern(left)
                right_pattern: nf.Pattern = self._convert_pattern(right)

                return self._resolve_notation('kore-And', and_symbol, [sort_symbol, left_pattern, right_pattern])
            case kore.App(symbol, sorts, args):
                symbol_pattern: nf.Pattern = self._resolve_symbol(symbol)
                sorts_pattern: list[nf.Pattern] = [self._resolve_symbol(sort) for sort in sorts]
                args_pattern: list[nf.Pattern] = [self._convert_pattern(arg) for arg in args]

                return self._resolve_notation(symbol, symbol_pattern, [*sorts_pattern, *args_pattern])
            case kore.EVar(_, _):
                # TODO: Revisit when we have sorting implemented!
                return self._resolve_evar(pattern)
            case kore.Top(sort):
                # TODO: Revisit when we have sorting implemented!
                return prop.Top()

        raise NotImplementedError(f'Pattern {pattern} is not supported')

    def _resolve_symbol(self, pattern: kore.Pattern | kore.Sort | str) -> nf.Symbol:
        """Resolve the symbol in the given pattern."""
        if isinstance(pattern, str):
            if pattern not in self._symbols:
                self._symbols[pattern] = nf.Symbol(name=len(self._symbols), pretty_name=pattern)
            return self._symbols[pattern]
        elif isinstance(pattern, kore.Sort):
            if pattern.name not in self._symbols:
                self._symbols[pattern.name] = nf.Symbol(name=len(self._symbols), pretty_name=pattern.name)
            return self._symbols[pattern.name]
        elif type(pattern) in self.CONST_SYMBOLS:
            return nf.Symbol(name=self.CONST_SYMBOLS.index(type(pattern)), pretty_name=f'KORE_{type(pattern).__name__}')
        elif isinstance(pattern, kore.Symbol):
            if pattern.symbol not in self._symbols:
                self._symbols[pattern.symbol] = nf.Symbol(name=len(self._symbols), pretty_name=pattern.symbol)
            return self._symbols[pattern.symbol]
        else:
            raise NotImplementedError(f'Pattern {pattern} is not supported')

    def _resolve_notation(self, name: str, symbol: nf.Symbol, arguments: list[nf.Pattern]) -> nf.Pattern:
        """Resolve the notation or make up one."""
        if name not in self._notations:
            new_notation = nf.make_up_notation(name, symbol, len(arguments))
            self._notations[name] = new_notation
        return self._notations[name](*arguments)

    def _resolve_evar(self, evar: kore.EVar) -> nf.EVar:
        """Resolve the evar in the given pattern."""
        if evar.name not in self._evars:
            self._evars[evar.name] = nf.EVar(name=len(self._evars))
        return self._evars[evar.name]
