from __future__ import annotations

from dataclasses import dataclass
from typing import TYPE_CHECKING

import proof_generation.proof as proof
import proof_generation.proofs.kore as kl
from proof_generation.k.kore_convertion.language_semantics import (
    AxiomType,
    ConvertedAxiom,
    KEquationalRule,
    KRewritingRule,
)
from proof_generation.pattern import EVar, Symbol
from proof_generation.proofs.definedness import functional
from proof_generation.proofs.substitution import Substitution, func_subst_axiom

if TYPE_CHECKING:
    from collections.abc import Iterator
    from types import TracebackType

    from proof_generation.k.kore_convertion.language_semantics import LanguageSemantics
    from proof_generation.k.kore_convertion.rewrite_steps import RewriteStepExpression
    from proof_generation.pattern import Pattern


Location = tuple[int, ...]


@dataclass
class SimplificationInfo:
    location: Location
    initial_pattern: Pattern  # Relative to previous in stack
    simplification_result: Pattern
    simplifications_remaining: int


class SimplificationPerformer:
    def __init__(self, language_semantics: LanguageSemantics, init_config: Pattern):
        self._language_semantics = language_semantics
        self._curr_config = init_config
        self._simplification_stack: list[SimplificationInfo] = []

    @property
    def simplified_configuration(self) -> Pattern:
        return self._curr_config

    @property
    def in_simplification(self) -> bool:
        return len(self._simplification_stack) > 0

    def update_configuration(self, new_current_configuration: Pattern) -> None:
        assert not self.in_simplification, 'Simplification is in progress'
        self._curr_config = new_current_configuration

    def apply_simplification(
        self, ordinal: int, substitution: dict[int, Pattern], location: Location
    ) -> SimplificationInfo:
        # Check that whether it is the first simplification or not
        if not self._simplification_stack:
            sub_pattern = self.get_subterm(location, self._curr_config)
        else:
            sub_pattern = self.get_subterm(location, self._simplification_stack[-1].simplification_result)

        # Get the rule and remove extra variables added by K in addition to the ones in the K file
        rule = self._language_semantics.get_axiom(ordinal)
        assert isinstance(rule, KEquationalRule), 'Simplification rule is not equational'
        base_substitutions = rule.substitutions_from_requires
        simplified_rhs = rule.right.apply_esubsts(base_substitutions)

        # Now apply the substitutions from the hint
        simplified_rhs = simplified_rhs.apply_esubsts(substitution)

        # Count the number of substitutions left
        simplifications_ramaining = self._language_semantics.count_simplifications(simplified_rhs)

        # Create the new info object and put it on top of the stack
        new_info = SimplificationInfo(location, sub_pattern, simplified_rhs, simplifications_ramaining)
        self._simplification_stack.append(new_info)

        return new_info

    def __enter__(self) -> SimplificationPerformer:
        return self

    def __exit__(
        self,
        exc_type: type[BaseException] | None,
        exc_value: BaseException | None,
        traceback: TracebackType | None,
    ) -> None:
        while self._simplification_stack and self._simplification_stack[-1].simplifications_remaining == 0:
            exhausted_info = self._simplification_stack.pop()
            if self._simplification_stack:
                # If the stack is non-empty, then we need to update the simplification on top of the stack
                last_info = self._simplification_stack[-1]
                last_info.simplifications_remaining -= 1
                last_info.simplification_result = self.update_subterm(
                    exhausted_info.location, last_info.simplification_result, exhausted_info.simplification_result
                )
            else:
                # If the stack is empty, then we need to update the current configuration as we processed the batch
                self._curr_config = self.update_subterm(
                    exhausted_info.location, self._curr_config, exhausted_info.simplification_result
                )

    def get_subterm(self, location: Location, pattern: Pattern) -> Pattern:
        # subpattern, left = self._get_subpattern_rec(list(location), pattern)
        _, found, location_remaining = self._subpattern_search_rec(list(location), pattern, None)
        assert not location_remaining, f'Location {location} is invalid for pattern {str(pattern)}'
        return found

    def update_subterm(self, location: Location, pattern: Pattern, plug: Pattern) -> Pattern:
        updated, _, location_remaining = self._subpattern_search_rec(list(location), pattern, plug)
        assert not location_remaining, f'Location {location} is invalid for pattern {str(pattern)}'
        return updated

    def _subpattern_search_rec(
        self, loc: list[int], pattern: Pattern, plug: Pattern | None = None
    ) -> tuple[Pattern, Pattern, list[int]]:
        """Search for the subpattern at the given location and replace it with the plug."""
        if not loc:
            return pattern if not plug else plug, pattern, loc

        next_turn, *loc_remaining = loc
        symbol, args_tuple = kl.deconstruct_nary_application(pattern)
        args_list = list(args_tuple)
        assert isinstance(symbol, Symbol)
        ksymbol = self._language_semantics.resolve_to_ksymbol(symbol)
        if ksymbol:
            next_turn += len(ksymbol.sort_params)
        assert len(args_list) > next_turn, f'Location {str(loc)} is invalid for pattern {str(pattern)}'

        # Replace the argument and return the application
        arg_with_plug_at_loc, orig_subpat_at_loc, loc_remaining = self._subpattern_search_rec(
            loc_remaining, args_list[next_turn], plug
        )
        args_list[next_turn] = arg_with_plug_at_loc

        if ksymbol:
            new_pattern_with_plug_at_loc = ksymbol.app(*args_list)
        else:
            new_pattern_with_plug_at_loc = kl.nary_app(symbol, len(args_list))(*args_list)
        return new_pattern_with_plug_at_loc, orig_subpat_at_loc, loc_remaining


class ExecutionProofExp(proof.ProofExp):
    def __init__(self, language_semantics: LanguageSemantics, init_config: Pattern):
        self._init_config = init_config
        self._curr_config = init_config
        self.language_semantics = language_semantics
        super().__init__(notations=list(language_semantics.notations))
        self.subst_proofexp = self.import_module(Substitution())
        self.kore_lemmas = self.import_module(kl.KoreLemmas())
        self._simplification_performer = SimplificationPerformer(self.language_semantics, self.current_configuration)

    @property
    def initial_configuration(self) -> Pattern:
        """Returns the initial configuration."""
        return self._init_config

    @staticmethod
    def collect_functional_axioms(
        language_semantics: LanguageSemantics, substitutions: dict[int, Pattern]
    ) -> list[ConvertedAxiom]:
        subst_axioms = []
        for pattern in substitutions.values():
            # Double-check that the pattern is a functional symbol and it is valid to generate the axiom
            sym, _ = kl.deconstruct_nary_application(pattern)
            assert isinstance(sym, Symbol), f'Pattern {pattern} is not supported'
            k_sym = language_semantics.resolve_to_ksymbol(sym)
            assert k_sym is not None
            assert k_sym.is_functional
            converted_pattern = functional(pattern)
            subst_axioms.append(ConvertedAxiom(AxiomType.FunctionalSymbol, converted_pattern))
        return subst_axioms

    def add_assumptions_for_rewrite_step(self, rule: KRewritingRule, substitutions: dict[int, Pattern]) -> None:
        """Add axioms to the definition."""
        # TODO: We don't use them until the substitutions are implemented
        func_axioms = ExecutionProofExp.collect_functional_axioms(self.language_semantics, substitutions)
        self.add_assumptions([axiom.pattern for axiom in func_axioms])
        self.add_axiom(rule.pattern)

    @property
    def current_configuration(self) -> Pattern:
        """Returns the current configuration."""
        return self._curr_config

    @staticmethod
    def assert_functional_pattern(semantics: LanguageSemantics, pattern: Pattern) -> None:
        sym, _ = kl.deconstruct_nary_application(pattern)
        # TODO: Should we also check that the arguments are functional?
        assert isinstance(sym, Symbol), f'Pattern {pattern} is not supported'
        k_sym = semantics.resolve_to_ksymbol(sym)
        assert k_sym is not None
        assert k_sym.is_functional

    def rewrite_event(self, rule: KRewritingRule, substitution: dict[int, Pattern]) -> proof.ProofThunk:
        """Extends the proof with an additional rewrite step."""
        # Construct and add claim
        claim = rule.pattern
        for name, plug in substitution.items():
            claim = claim.apply_esubst(name, plug)
        self.add_claim(claim)
        sort, lhs, rhs = kl.kore_rewrites.assert_matches(claim)

        # Check that the lhs equals the current configuration
        assert (
            lhs == self.current_configuration
        ), f'The current configuration {str(self.current_configuration)} does not equal {str(lhs)}, the lhs of an instance of rule {str(rule.pattern)}'

        # Add the axioms/assumptions
        self.add_axiom(rule.pattern)
        for name, plug in substitution.items():
            self.assert_functional_pattern(self.language_semantics, plug)
            self.add_assumption(functional(plug))
            # TODO: Get rid of this hack:
            self.subst_proofexp.add_axiom(func_subst_axiom(name))

        # Compute the proof
        step_pf = self.load_axiom(rule.pattern)
        for name, plug in substitution.items():
            functional_assumption = self.load_axiom(functional(plug))
            universalized = self.subst_proofexp.universal_gen(step_pf, EVar(name))
            step_pf = self.subst_proofexp.functional_subst(functional_assumption, universalized, EVar(name))

        # Add the proof
        self.add_proof_expression(step_pf)
        self._curr_config = rhs

        # Update the current configuration
        self._simplification_performer.update_configuration(self._curr_config)

        return step_pf

    def simplification_event(self, ordinal: int, substitution: dict[int, Pattern], location: Location) -> None:
        with self._simplification_performer as performer:
            performer.apply_simplification(ordinal, substitution, location)
            # TODO: Do some proving here ...

        # Update the current configuration
        self._curr_config = self._simplification_performer.simplified_configuration

    def finalize(self) -> None:
        """Prepare proof expression for the final reachability claim"""
        # TODO: Prove the final reachability claim
        return

    @staticmethod
    def from_proof_hints(
        hints: Iterator[RewriteStepExpression], language_semantics: LanguageSemantics
    ) -> proof.ProofExp:
        """Constructs a proof expression from a list of rewrite hints."""
        proof_expr: ExecutionProofExp | None = None
        for hint in hints:
            if proof_expr is None:
                proof_expr = ExecutionProofExp(language_semantics, hint.configuration_before)

            if isinstance(hint.axiom, KRewritingRule):
                proof_expr.rewrite_event(hint.axiom, hint.substitutions)
            else:
                # TODO: Remove the stub
                raise NotImplementedError('TODO: Add support for equational rules')

        if proof_expr is None:
            print('WARNING: The proof expression is empty, ho hints were provided.')
            return proof.ProofExp(notations=list(language_semantics.notations))
        else:
            return proof_expr
