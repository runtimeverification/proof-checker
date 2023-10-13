from __future__ import annotations

from collections.abc import Callable

import pyk.kore.syntax as kore

import proof_generation.pattern as nf
import proof_generation.proof as proof
import proof_generation.proofs.propositional as prop

ProofMethod = Callable[[proof.ProofExp], proof.Proved]


class ExecutionProofGen:
    CONST_SYMBOLS: tuple[type[kore.Pattern], ...] = (kore.And, kore.Top, kore.EVar)

    def __init__(self, kore_definition: kore.Definition, module_name: str) -> None:
        self._definition = kore_definition
        self._module = module_name

        self._symbols: dict[str, nf.Symbol] = {}
        self._evars: dict[str, nf.EVar] = {}
        self._svars: dict[str, nf.SVar] = {}
        self._metavars: dict[str, nf.MetaVar] = {}
        self._notations: dict[str, type[nf.Notation]] = {}
        self._axioms: list[nf.Pattern] = []
        self._claims: list[nf.Pattern] = []
        self._proofs: list[ProofMethod] = []

        # Prepare for the gamma phase
        # Find the relevant rule and the corresponding substitution
        axioms_for_rules = self._find_rules_for_convertion()
        for axiom in axioms_for_rules:
            self._axioms.append(self._convert_axiom(axiom))

    def prove_rewrite_step(self, initial_config: kore.Pattern, next_config: kore.Pattern) -> None:
        """Take a single rewrite step and emit a proof for it."""
        # emit a proof for taking a single step
        # returns the final pattern
        conf1 = self._convert_pattern(initial_config)
        conf2 = self._convert_pattern(next_config)

        # Make claim
        claim = nf.Implication(conf1, conf2)
        self._claims.append(claim)

        # Make proof
        # Required axiom
        axiom = self._axioms[0]

        # TODO: How are we supposed to figure out instantiations?
        assert (
            isinstance(initial_config, kore.App)
            and isinstance(initial_config.args[0], kore.App)
            and isinstance(initial_config.args[0].args[0], kore.App)
        )
        kseq_pattern = self._convert_pattern(initial_config.args[0].args[0].args[1])
        zero_pattern = self._convert_pattern(initial_config.args[1])

        def proof_transition(proof_expr: proof.ProofExp) -> proof.Proved:
            """Prove the transition between two configurations."""
            proof_expr.interpreter.pattern(kseq_pattern)
            proof_expr.interpreter.pattern(zero_pattern)
            return proof_expr.interpreter.instantiate(proof_expr.load_axiom(axiom), {0: kseq_pattern, 1: zero_pattern})

        self._proofs.append(proof_transition)

    def compose_proofs(self) -> type[proof.ProofExp]:
        """Compose the proofs for all steps."""
        extracted_axioms: list[nf.Pattern] = list(self._axioms)
        extracted_claims: list[nf.Pattern] = list(self._claims)
        composed_proofs: list[ProofMethod] = list(self._proofs)

        class TranslatedProofSkeleton(proof.ProofExp):
            @staticmethod
            def axioms() -> list[nf.Pattern]:
                return extracted_axioms

            @staticmethod
            def claims() -> list[nf.Pattern]:
                return extracted_claims

            def proof_expressions(self) -> list[proof.ProvedExpression]:
                def make_function(obj: TranslatedProofSkeleton, func: ProofMethod) -> proof.ProvedExpression:
                    return lambda: func(obj)

                return [make_function(self, proof_func) for proof_func in composed_proofs]

        return TranslatedProofSkeleton

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
        # TODO: Remove this step below
        # Preprocess the actual pattern by throwing out side conditions for now
        pattern = axiom.pattern
        assert isinstance(pattern, kore.Rewrites)
        assert isinstance(pattern.left, kore.And)
        assert isinstance(pattern.right, kore.And)
        preprocessed_pattern = kore.Rewrites(pattern.sort, pattern.left.left, pattern.right.left)

        new_pattern = self._convert_pattern(preprocessed_pattern)
        return new_pattern

    def _convert_pattern(self, pattern: kore.Pattern) -> nf.Pattern:
        """Convert the given pattern to the pattern in the new format."""
        # TODO: Double check everything below!
        match pattern:
            case kore.Rewrites(_, left, right):
                # TODO: Sort is ignored for now.
                left_rw_pattern = self._convert_pattern(left)
                right_rw_pattern = self._convert_pattern(right)
                return nf.Implication(left_rw_pattern, right_rw_pattern)
            case kore.And(sort, left, right):
                and_symbol: nf.Symbol = self._resolve_symbol(pattern)
                sort_symbol: nf.Pattern = self._resolve_symbol(sort)
                left_and_pattern: nf.Pattern = self._convert_pattern(left)
                right_and_pattern: nf.Pattern = self._convert_pattern(right)

                return self._resolve_notation(
                    'kore-And', and_symbol, [sort_symbol, left_and_pattern, right_and_pattern]
                )
            case kore.App(symbol, _, args):
                symbol_pattern: nf.Symbol = self._resolve_symbol(symbol)
                args_pattern: list[nf.Pattern] = [self._convert_pattern(arg) for arg in args]

                # TODO: We need to work with Fake notations, but for now it doesn't work
                # sorts_pattern: list[nf.Pattern] = [self._resolve_symbol(sort) for sort in sorts]
                # return self._resolve_notation(symbol, symbol_pattern, [*sorts_pattern, *args_pattern])
                def chained_application(pattern: nf.Pattern, args: list[nf.Pattern]) -> nf.Pattern:
                    """Simplify generating chains of applications for symbols with several args."""
                    if len(args) == 0:
                        return pattern
                    else:
                        current_callable = pattern
                        arguments_left = args
                        while len(arguments_left) > 0:
                            next_one, *arguments_left = arguments_left
                            current_callable = nf.Application(current_callable, next_one)
                        return current_callable

                return chained_application(symbol_pattern, args_pattern)
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
                self._symbols[pattern] = nf.Symbol(name=len(self._symbols), pretty_name=pattern)
            return self._symbols[pattern]
        elif isinstance(pattern, kore.Sort):
            if pattern.name not in self._symbols:
                self._symbols[pattern.name] = nf.Symbol(name=len(self._symbols), pretty_name=pattern.name)
            return self._symbols[pattern.name]
        elif type(pattern) in self.CONST_SYMBOLS:
            return nf.Symbol(name=self.CONST_SYMBOLS.index(type(pattern)), pretty_name=f'KORE_{type(pattern).__name__}')
        elif isinstance(pattern, kore.Symbol):
            if pattern.name not in self._symbols:
                self._symbols[pattern.name] = nf.Symbol(name=len(self._symbols), pretty_name=pattern.name)
            return self._symbols[pattern.name]
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

    def _resolve_metavar(self, name: str) -> nf.MetaVar:
        """Resolve the metavar in the given pattern."""
        if name not in self._metavars:
            self._metavars[name] = nf.MetaVar(name=len(self._metavars))
        return self._metavars[name]
