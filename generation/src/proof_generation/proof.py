from __future__ import annotations

from collections import namedtuple
from collections.abc import Callable
from dataclasses import dataclass
from enum import Enum
from typing import BinaryIO, TextIO

from proof_generation.instruction import Instruction
from proof_generation.pattern import (
    Application,
    ESubst,
    EVar,
    Exists,
    Implication,
    MetaVar,
    Mu,
    Pattern,
    SSubst,
    SVar,
    Symbol,
)


class ExecutionPhase(Enum):
    Gamma = 0
    Claim = 1
    Proof = 2


@dataclass
class Proved:
    conclusion: Pattern

    def assertc(self, pattern: Pattern) -> Proved:
        assert self.conclusion == pattern
        return self

    def __str__(self) -> str:
        return str(self.conclusion)


# Proof Expressions
# =================


class BasicInterpreter:
    """A stateless proof interpreter. It only checks conclusions."""

    def __init__(self, phase: ExecutionPhase):
        self.phase = phase

    def into_claim_phase(self) -> None:
        assert self.phase == ExecutionPhase.Gamma
        self.phase = ExecutionPhase.Claim

    def into_proof_phase(self) -> None:
        assert self.phase == ExecutionPhase.Claim
        self.phase = ExecutionPhase.Proof

    def evar(self, id: int) -> Pattern:
        return EVar(id)

    def svar(self, id: int) -> Pattern:
        return SVar(id)

    def symbol(self, id: int) -> Pattern:
        return Symbol(id)

    def metavar(
        self,
        id: int,
        e_fresh: tuple[EVar, ...] = (),
        s_fresh: tuple[SVar, ...] = (),
        positive: tuple[SVar, ...] = (),
        negative: tuple[SVar, ...] = (),
        application_context: tuple[EVar, ...] = (),
    ) -> Pattern:
        return MetaVar(id, e_fresh, s_fresh, positive, negative, application_context)

    def implies(self, left: Pattern, right: Pattern) -> Pattern:
        return Implication(left, right)

    def app(self, left: Pattern, right: Pattern) -> Pattern:
        return Application(left, right)

    def exists(self, var: int, subpattern: Pattern) -> Pattern:
        return Exists(EVar(var), subpattern)

    def esubst(self, evar_id: int, pattern: MetaVar | ESubst | SSubst, plug: Pattern) -> Pattern:
        return ESubst(pattern, EVar(evar_id), plug)

    def ssubst(self, svar_id: int, pattern: MetaVar | ESubst | SSubst, plug: Pattern) -> Pattern:
        return SSubst(pattern, SVar(svar_id), plug)

    def mu(self, var: int, subpattern: Pattern) -> Pattern:
        return Mu(SVar(var), subpattern)

    def pattern(self, p: Pattern) -> Pattern:
        match p:
            case EVar(name):
                return self.evar(name)
            case SVar(name):
                return self.svar(name)
            case Symbol(name):
                return self.symbol(name)
            case Implication(left, right):
                return self.implies(self.pattern(left), self.pattern(right))
            case Application(left, right):
                return self.app(self.pattern(left), self.pattern(right))
            case Exists(var, subpattern):
                return self.exists(var.name, self.pattern(subpattern))
            case Mu(var, subpattern):
                return self.mu(var.name, self.pattern(subpattern))
            case MetaVar(name, e_fresh, s_fresh, positive, negative, app_ctx_holes):
                # TODO: The results should be passed to self.metavar
                self.patterns(e_fresh)
                self.patterns(s_fresh)
                self.patterns(positive)
                self.patterns(negative)
                self.patterns(app_ctx_holes)

                return self.metavar(name, e_fresh, s_fresh, positive, negative, app_ctx_holes)

        raise NotImplementedError(f'{type(p)}')

    def patterns(self, ps: tuple[Pattern, ...]) -> tuple[Pattern, ...]:
        return tuple(self.pattern(p) for p in ps)

    def prop1(self) -> Proved:
        phi0: MetaVar = MetaVar(0)
        phi1: MetaVar = MetaVar(1)
        return Proved(Implication(phi0, Implication(phi1, phi0)))

    def prop2(self) -> Proved:
        phi0: MetaVar = MetaVar(0)
        phi1: MetaVar = MetaVar(1)
        phi2: MetaVar = MetaVar(2)
        return Proved(
            Implication(
                Implication(phi0, Implication(phi1, phi2)),
                Implication(Implication(phi0, phi1), Implication(phi0, phi2)),
            ),
        )

    def prop3(self) -> Proved:
        phi0: MetaVar = MetaVar(0)
        bot: Pattern = Mu(SVar(0), SVar(0))
        return Proved(Implication(Implication(Implication(phi0, bot), bot), phi0))

    def modus_ponens(self, left: Proved, right: Proved) -> Proved:
        left_conclusion = left.conclusion
        assert isinstance(left_conclusion, Implication)
        assert left_conclusion.left == right.conclusion, (left_conclusion.left, right.conclusion)
        return Proved(left_conclusion.right)

    def instantiate(self, proved: Proved, delta: dict[int, Pattern]) -> Proved:
        return Proved(proved.conclusion.instantiate(delta))

    def instantiate_notation(self, pattern: Pattern, delta: dict[int, Pattern]) -> Pattern:
        return pattern.instantiate(delta)

    def pop(self, term: Pattern | Proved) -> None:
        ...

    def save(self, id: str, term: Pattern | Proved) -> None:
        ...

    def load(self, id: str, term: Pattern | Proved) -> None:
        ...

    def publish_proof(self, term: Proved) -> None:
        assert self.phase == ExecutionPhase.Proof
        ...

    def publish_axiom(self, term: Pattern) -> None:
        assert self.phase == ExecutionPhase.Gamma
        ...

    def publish_claim(self, term: Pattern) -> None:
        assert self.phase == ExecutionPhase.Claim
        ...


@dataclass
class Claim:
    pattern: Pattern


class StatefulInterpreter(BasicInterpreter):
    """A Proof interpreter that also keeps track of the verifier state,
    such as the memory, stack and claims remaining.
    """

    claims: list[Claim]
    stack: list[Pattern | Proved]
    memory: list[Pattern | Proved]

    def __init__(
        self,
        phase: ExecutionPhase,
        claims: list[Claim] | None = None,
    ) -> None:
        super().__init__(phase=phase)
        self.stack = []
        self.memory = []
        self.claims = claims if claims else []

    def into_claim_phase(self) -> None:
        self.stack = []
        super().into_claim_phase()

    def into_proof_phase(self) -> None:
        self.stack = []
        super().into_proof_phase()

    def print_state(self) -> None:
        for i, item in enumerate(self.stack):
            print(i, item)

    def evar(self, id: int) -> Pattern:
        ret = super().evar(id)
        self.stack.append(ret)
        return ret

    def svar(self, id: int) -> Pattern:
        ret = super().svar(id)
        self.stack.append(ret)
        return ret

    def symbol(self, id: int) -> Pattern:
        ret = super().symbol(id)
        self.stack.append(ret)
        return ret

    def metavar(
        self,
        id: int,
        e_fresh: tuple[EVar, ...] = (),
        s_fresh: tuple[SVar, ...] = (),
        positive: tuple[SVar, ...] = (),
        negative: tuple[SVar, ...] = (),
        application_context: tuple[EVar, ...] = (),
    ) -> Pattern:
        ret = super().metavar(id, e_fresh, s_fresh, positive, negative, application_context)
        self.stack.append(ret)
        return ret

    def implies(self, left: Pattern, right: Pattern) -> Pattern:
        *self.stack, expected_left, expected_right = self.stack
        assert expected_left == left
        assert expected_right == right
        ret = super().implies(left, right)
        self.stack.append(ret)
        return ret

    def app(self, left: Pattern, right: Pattern) -> Pattern:
        *self.stack, expected_left, expected_right = self.stack
        assert expected_left == left
        assert expected_right == right
        ret = super().app(left, right)
        self.stack.append(ret)
        return ret

    def exists(self, var: int, subpattern: Pattern) -> Pattern:
        *self.stack, expected_subpattern = self.stack
        assert expected_subpattern == subpattern
        ret = super().exists(var, subpattern)
        self.stack.append(ret)
        return ret

    def mu(self, var: int, subpattern: Pattern) -> Pattern:
        *self.stack, expected_subpattern = self.stack
        assert expected_subpattern == subpattern
        ret = super().mu(var, subpattern)
        self.stack.append(ret)
        return ret

    def esubst(self, evar_id: int, pattern: MetaVar | ESubst | SSubst, plug: Pattern) -> Pattern:
        *self.stack, expected_plug, expected_pattern = self.stack
        assert expected_pattern == pattern
        assert expected_plug == plug
        ret = super().esubst(evar_id, pattern, plug)
        self.stack.append(ret)
        return ret

    def ssubst(self, svar_id: int, pattern: MetaVar | ESubst | SSubst, plug: Pattern) -> Pattern:
        *self.stack, expected_plug, expected_pattern = self.stack
        assert expected_pattern == pattern
        assert expected_plug == plug
        ret = super().ssubst(svar_id, pattern, plug)
        self.stack.append(ret)
        return ret

    def prop1(self) -> Proved:
        ret = super().prop1()
        self.stack.append(ret)
        return ret

    def prop2(self) -> Proved:
        ret = super().prop2()
        self.stack.append(ret)
        return ret

    def prop3(self) -> Proved:
        ret = super().prop3()
        self.stack.append(ret)
        return ret

    def modus_ponens(self, left: Proved, right: Proved) -> Proved:
        *self.stack, expected_left, expected_right = self.stack
        assert expected_left == left, f'expected: {expected_left}\ngot: {left}'
        assert expected_right == right, f'expected: {expected_right}\ngot: {right}'
        ret = super().modus_ponens(left, right)
        self.stack.append(ret)
        return ret

    def instantiate(self, proved: Proved, delta: dict[int, Pattern]) -> Proved:
        *self.stack, expected_proved = self.stack
        expected_plugs = self.stack[-len(delta) :]
        self.stack = self.stack[: -len(delta)]

        assert expected_proved == proved, f'expected: {expected_proved}\ngot: {proved}'
        assert expected_plugs == list(delta.values()), f'expected: {expected_plugs}\ngot: {list(delta.values())}'
        ret = super().instantiate(proved, delta)
        self.stack.append(ret)
        return ret

    def instantiate_notation(self, pattern: Pattern, delta: dict[int, Pattern]) -> Pattern:
        *self.stack, expected_pattern = self.stack
        expected_plugs = self.stack[-len(delta) :]
        self.stack = self.stack[: -len(delta)]

        assert expected_pattern == pattern, f'expected: {expected_pattern}\ngot: {pattern}'
        assert expected_plugs == list(delta.values()), f'expected: {expected_plugs}\ngot: {list(delta.values())}'
        ret = super().instantiate_notation(pattern, delta)
        self.stack.append(ret)
        return ret

    def pop(self, term: Pattern | Proved) -> None:
        assert self.stack[-1] == term, f'expected: {self.stack[-1]}\ngot: {term}'
        self.stack.pop()
        super().pop(term)

    def save(self, id: str, term: Pattern | Proved) -> None:
        assert self.stack[-1] == term, f'expected: {self.stack[-1]}\ngot: {term}'
        self.memory.append(term)
        super().save(id, term)

    def load(self, id: str, term: Pattern | Proved) -> None:
        assert term in self.memory
        self.stack.append(term)
        super().load(id, term)

    def publish_proof(self, proved: Proved) -> None:
        super().publish_proof(proved)
        expected_claim, *self.claims = self.claims
        assert proved.conclusion == expected_claim.pattern, f'{proved.conclusion, expected_claim.pattern}'
        assert self.stack[-1] == proved

    def publish_axiom(self, axiom: Pattern) -> None:
        self.memory.append(Proved(axiom))
        super().publish_axiom(axiom)
        assert self.stack[-1] == axiom

    def publish_claim(self, pattern: Pattern) -> None:
        super().publish_claim(pattern)
        assert self.stack[-1] == pattern


class CountingInterpreter(StatefulInterpreter):
    Stats = namedtuple('Stats', ['uses', 'complexity_score', 'complexity', 'used_patterns'])

    def __init__(
        self,
        phase: ExecutionPhase,
        claims: list[Claim] | None = None,
    ) -> None:
        super().__init__(phase=phase, claims=claims)
        self._max_allowed_slots = 256
        self._finalized = False
        self._pattern_usage: dict[Pattern, CountingInterpreter.Stats] = {}
        self._saved_by_implementation: set[Pattern] = set()
        self._suggested_for_memoization: set[Pattern] = set()

    @property
    def max_memory_slots(self) -> int:
        return self._max_allowed_slots

    @property
    def finalized(self) -> bool:
        return self._finalized

    @property
    def suggested_for_memoization(self) -> set[Pattern]:
        assert self.finalized, 'Suggestions cannot be accessed until the interpreter is finalized'
        return set(self._suggested_for_memoization)

    def finalize(self) -> set[Pattern]:
        assert not self._finalized
        self._max_allowed_slots -= len(self.memory)
        memoized = [p.conclusion if isinstance(p, Proved) else p for p in self.memory]

        def get_suitable() -> list[Pattern]:
            already_selected = [
                p for p in memoized if p not in self._suggested_for_memoization and p in self._pattern_usage
            ]
            if already_selected:
                return already_selected
            else:
                suitable = [
                    pattern
                    for pattern in self._pattern_usage
                    if self._pattern_usage[pattern].uses > 1 and pattern not in self._suggested_for_memoization
                ]
                suitable.sort(key=lambda pattern: self._pattern_usage[pattern].complexity_score, reverse=True)
                return suitable

        # Now we can compute iteratively suggested patterns
        counter = self._max_allowed_slots

        # Update the complexity score for each pattern
        for pattern in self._pattern_usage:
            self._compute_complexity_score(pattern)

        todo = get_suitable()
        while counter > 0 and len(todo) > 0:
            # Sorting patterns according to multiplication of the number of uses and number of atomic elements in the pattern
            # This should give us the the size of thw whole stack which is occupied by the pattern construction operations
            pattern = todo.pop(0)
            pattern_stats = self._pattern_usage[pattern]
            self._suggested_for_memoization.add(pattern)
            counter -= 1

            # Update related stats
            dependencies = {p for p, stats in self._pattern_usage.items() if pattern in stats.used_patterns}
            requires_updating = set()
            # Now, when we memoized the pattern, patterns that contains this one become less complex,
            # so we need to update their complexity and later update the score
            for dependency in dependencies:
                old_stats = self._pattern_usage[dependency]
                requires_updating.add(dependency)
                self._pattern_usage[dependency] = self._pattern_usage[dependency]._replace(
                    complexity=old_stats.complexity - pattern_stats.complexity * old_stats.used_patterns[pattern] + 1
                )

                # We also start using less patterns that are used by the memoized one
                for child in pattern_stats.used_patterns:
                    self._pattern_usage[dependency].used_patterns[child] -= (
                        pattern_stats.used_patterns[child] * old_stats.used_patterns[pattern]
                    )

            # As we memoized the pattern, patterns that are used by this one become less frequently used,
            # so we need to update their usage and later update the score metric
            for used in pattern_stats.used_patterns:
                requires_updating.add(used)
                old_stats = self._pattern_usage[used]
                self._pattern_usage[used] = self._pattern_usage[used]._replace(
                    uses=old_stats.uses - pattern_stats.used_patterns[used] * pattern_stats.uses
                )

            # Memoized pattern becomes atomic
            self._pattern_usage[pattern] = self._pattern_usage[pattern]._replace(complexity=1)

            # Recalculate scores for all patterns
            for pattern in requires_updating:
                self._compute_complexity_score(pattern)

            # Recalculate options
            todo = get_suitable()

        self._finalized = True
        return self.suggested_for_memoization

    def evar(self, id: int) -> Pattern:
        ret = super().evar(id)
        self._collect_patterns(ret)
        return ret

    def svar(self, id: int) -> Pattern:
        ret = super().svar(id)
        self._collect_patterns(ret)
        return ret

    def symbol(self, id: int) -> Pattern:
        ret = super().symbol(id)
        self._collect_patterns(ret)
        return ret

    def metavar(
        self,
        id: int,
        e_fresh: tuple[EVar, ...] = (),
        s_fresh: tuple[SVar, ...] = (),
        positive: tuple[SVar, ...] = (),
        negative: tuple[SVar, ...] = (),
        application_context: tuple[EVar, ...] = (),
    ) -> Pattern:
        ret = super().metavar(id, e_fresh, s_fresh, positive, negative, application_context)
        self._collect_patterns(ret)
        return ret

    def implies(self, left: Pattern, right: Pattern) -> Pattern:
        ret = super().implies(left, right)
        self._collect_patterns(ret)
        return ret

    def app(self, left: Pattern, right: Pattern) -> Pattern:
        ret = super().app(left, right)
        self._collect_patterns(ret)
        return ret

    def exists(self, var: int, subpattern: Pattern) -> Pattern:
        ret = super().exists(var, subpattern)
        self._collect_patterns(ret)
        return ret

    def mu(self, var: int, subpattern: Pattern) -> Pattern:
        ret = super().mu(var, subpattern)
        self._collect_patterns(ret)
        return ret

    def esubst(self, evar_id: int, pattern: MetaVar | ESubst | SSubst, plug: Pattern) -> Pattern:
        ret = super().esubst(evar_id, pattern, plug)
        self._collect_patterns(ret)
        return ret

    def ssubst(self, svar_id: int, pattern: MetaVar | ESubst | SSubst, plug: Pattern) -> Pattern:
        ret = super().ssubst(svar_id, pattern, plug)
        self._collect_patterns(ret)
        return ret

    def prop1(self) -> Proved:
        ret = super().prop1()
        self._collect_patterns(ret.conclusion)
        return ret

    def prop2(self) -> Proved:
        ret = super().prop2()
        self._collect_patterns(ret.conclusion)
        return ret

    def prop3(self) -> Proved:
        ret = super().prop3()
        self._collect_patterns(ret.conclusion)
        return ret

    def modus_ponens(self, left: Proved, right: Proved) -> Proved:
        ret = super().modus_ponens(left, right)
        self._collect_patterns(ret.conclusion)
        return ret

    def instantiate(self, proved: Proved, delta: dict[int, Pattern]) -> Proved:
        ret = super().instantiate(proved, delta)
        self._collect_patterns(ret.conclusion)
        return ret

    def instantiate_notation(self, pattern: Pattern, delta: dict[int, Pattern]) -> Pattern:
        ret = super().instantiate_notation(pattern, delta)
        self._collect_patterns(ret)
        return ret

    def _collect_patterns(self, p: Pattern) -> None:
        children: list[Pattern] = []
        if isinstance(p, Implication):
            children.append(p.left)
            children.append(p.right)
        elif isinstance(p, Application):
            children.append(p.left)
            children.append(p.right)
        elif isinstance(p, Exists):
            children.append(p.subpattern)
        elif isinstance(p, Mu):
            children.append(p.subpattern)

        if p not in self._pattern_usage:
            self._pattern_usage[p] = CountingInterpreter.Stats(
                uses=1, complexity_score=0, complexity=1, used_patterns={}
            )

            # Go deeper recusively
            for child in children:
                self._collect_patterns(child)

            # Increase the complexity score for each child plus one
            self._pattern_usage[p] = self._pattern_usage[p]._replace(
                complexity=self._pattern_usage[p].complexity
                + sum(self._pattern_usage[child].complexity for child in children)
            )

            # Add usages of children to the pattern
            stats = self._pattern_usage[p]
            for child in children:
                child_stats = self._pattern_usage[child]
                stats.used_patterns.setdefault(child, 0)
                stats.used_patterns[child] += 1
                for child_uses, number in child_stats.used_patterns.items():
                    stats.used_patterns.setdefault(child_uses, 0)
                    stats.used_patterns[child_uses] += number
        else:
            self._pattern_usage[p] = self._pattern_usage[p]._replace(uses=self._pattern_usage[p].uses + 1)

    def _compute_complexity_score(self, p: Pattern) -> None:
        entries = self._pattern_usage[p].uses
        complexity = self._pattern_usage[p].complexity

        self._pattern_usage[p] = self._pattern_usage[p]._replace(complexity_score=entries * complexity)


class SerializingInterpreter(StatefulInterpreter):
    def __init__(
        self,
        phase: ExecutionPhase,
        out: BinaryIO,
        claims: list[Claim] | None = None,
    ) -> None:
        super().__init__(phase=phase, claims=claims)
        self.out = out

    def evar(self, id: int) -> Pattern:
        ret = super().evar(id)
        self.out.write(bytes([Instruction.EVar, id]))
        return ret

    def svar(self, id: int) -> Pattern:
        ret = super().svar(id)
        self.out.write(bytes([Instruction.SVar, id]))
        return ret

    def symbol(self, id: int) -> Pattern:
        ret = super().symbol(id)
        self.out.write(bytes([Instruction.Symbol, id]))
        return ret

    def metavar(
        self,
        id: int,
        e_fresh: tuple[EVar, ...] = (),
        s_fresh: tuple[SVar, ...] = (),
        positive: tuple[SVar, ...] = (),
        negative: tuple[SVar, ...] = (),
        application_context: tuple[EVar, ...] = (),
    ) -> Pattern:
        ret = super().metavar(id, e_fresh, s_fresh, positive, negative, application_context)
        lists: list[tuple[EVar, ...] | tuple[SVar, ...]] = [e_fresh, s_fresh, positive, negative, application_context]

        if sum([len(list) for list in lists]) == 0:
            # If all arrays are empty, metavar is "clean", we use a more succint instruction
            self.out.write(bytes([Instruction.CleanMetaVar, id]))
        else:
            self.out.write(bytes([Instruction.MetaVar, id]))
            for list in lists:
                self.out.write(bytes([len(list), *[var.name for var in list]]))
        return ret

    def implies(self, left: Pattern, right: Pattern) -> Pattern:
        ret = super().implies(left, right)
        self.out.write(bytes([Instruction.Implication]))
        return ret

    def app(self, left: Pattern, right: Pattern) -> Pattern:
        ret = super().app(left, right)
        self.out.write(bytes([Instruction.Application]))
        return ret

    def exists(self, var: int, subpattern: Pattern) -> Pattern:
        ret = super().exists(var, subpattern)
        self.out.write(bytes([Instruction.Exists, var]))
        return ret

    def mu(self, var: int, subpattern: Pattern) -> Pattern:
        ret = super().mu(var, subpattern)
        self.out.write(bytes([Instruction.Mu, var]))
        return ret

    def esubst(self, evar_id: int, pattern: MetaVar | ESubst | SSubst, plug: Pattern) -> Pattern:
        ret = super().esubst(evar_id, pattern, plug)
        self.out.write(bytes([Instruction.ESubst, evar_id]))
        return ret

    def ssubst(self, svar_id: int, pattern: MetaVar | ESubst | SSubst, plug: Pattern) -> Pattern:
        ret = super().ssubst(svar_id, pattern, plug)
        self.out.write(bytes([Instruction.SSubst, svar_id]))
        return ret

    def prop1(self) -> Proved:
        ret = super().prop1()
        self.out.write(bytes([Instruction.Prop1]))
        return ret

    def prop2(self) -> Proved:
        ret = super().prop2()
        self.out.write(bytes([Instruction.Prop2]))
        return ret

    def prop3(self) -> Proved:
        ret = super().prop3()
        self.out.write(bytes([Instruction.Prop3]))
        return ret

    def modus_ponens(self, left: Proved, right: Proved) -> Proved:
        ret = super().modus_ponens(left, right)
        self.out.write(bytes([Instruction.ModusPonens]))
        return ret

    def instantiate(self, proved: Proved, delta: dict[int, Pattern]) -> Proved:
        ret = super().instantiate(proved, delta)
        self.out.write(bytes([Instruction.Instantiate, len(delta), *reversed(delta.keys())]))
        return ret

    def instantiate_notation(self, pattern: Pattern, delta: dict[int, Pattern]) -> Pattern:
        ret = super().instantiate_notation(pattern, delta)
        self.out.write(bytes([Instruction.Instantiate, len(delta), *reversed(delta.keys())]))
        return ret

    def pop(self, term: Pattern | Proved) -> None:
        super().pop(term)
        self.out.write(bytes([Instruction.Pop]))

    def save(self, id: str, term: Pattern | Proved) -> None:
        ret = super().save(id, term)
        self.out.write(bytes([Instruction.Save]))
        return ret

    def load(self, id: str, term: Pattern | Proved) -> None:
        ret = super().load(id, term)
        self.out.write(bytes([Instruction.Load, self.memory.index(term)]))
        return ret

    def publish_proof(self, proved: Proved) -> None:
        super().publish_proof(proved)
        self.out.write(bytes([Instruction.Publish]))

    def publish_axiom(self, axiom: Pattern) -> None:
        super().publish_axiom(axiom)
        self.out.write(bytes([Instruction.Publish]))

    def publish_claim(self, pattern: Pattern) -> None:
        super().publish_claim(pattern)
        self.out.write(bytes([Instruction.Publish]))


class MemoizingInterpreter(SerializingInterpreter):
    def __init__(
        self,
        phase: ExecutionPhase,
        out: BinaryIO,
        claims: list[Claim] | None = None,
        patterns_for_memoization: set[Pattern] | None = None,
    ) -> None:
        super().__init__(phase, out, claims)
        self._patterns_for_memoization: set[Pattern]
        if patterns_for_memoization is None:
            self._patterns_for_memoization = set()
        else:
            self._patterns_for_memoization = patterns_for_memoization

    def pattern(self, p: Pattern) -> Pattern:
        if p in self.memory:
            self.load(str(p), p)
            return p
        elif p in self._patterns_for_memoization:
            ret = super().pattern(p)
            self.save(repr(p), p)
            return ret
        else:
            return super().pattern(p)


class PrettyPrintingInterpreter(StatefulInterpreter):
    def __init__(
        self,
        phase: ExecutionPhase,
        out: TextIO,
        claims: list[Claim] | None = None,
    ) -> None:
        super().__init__(phase=phase, claims=claims)
        self.out = out
        self._notation: dict[str, Pattern] = {}

    def plug_in_notation(self, notation: dict[str, Pattern]) -> None:
        self._notation = notation

    @property
    def notation(self) -> dict[Pattern, str]:
        return {v: k for k, v in self._notation.items()}

    @staticmethod
    def pretty(print_stack: bool = True) -> Callable:
        def decorator(func: Callable) -> Callable:
            def wrapper(*args: Pattern | dict | PrettyPrintingInterpreter, **kwargs: dict) -> Pattern | Proved:
                self, *nargs = args
                assert isinstance(self, PrettyPrintingInterpreter)
                # Find and call the super method.
                result = getattr(super(PrettyPrintingInterpreter, self), func.__name__)(*nargs, **kwargs)
                # Call the pretty printing function.
                func(self, *nargs, **kwargs)
                self.out.write('\n')
                # Print stack
                if print_stack:
                    self.print_stack()
                return result

            return wrapper

        return decorator

    @pretty()
    def evar(self, id: int) -> None:
        self.out.write('EVar ')
        self.out.write(str(id))

    @pretty()
    def svar(self, id: int) -> None:
        self.out.write('SVar ')
        self.out.write(str(id))

    @pretty()
    def symbol(self, id: int) -> None:
        self.out.write('Symbol ')
        self.out.write(str(id))

    @pretty()
    def metavar(
        self,
        id: int,
        e_fresh: tuple[EVar, ...] = (),
        s_fresh: tuple[SVar, ...] = (),
        positive: tuple[SVar, ...] = (),
        negative: tuple[SVar, ...] = (),
        application_context: tuple[EVar, ...] = (),
    ) -> None:
        def write_list(name: str, lst: tuple[EVar, ...] | tuple[SVar, ...]) -> None:
            # Don't print empty arguments
            if len(lst) == 0:
                return
            self.out.write(f'{name}, len={len(lst)} ')
            for item in lst:
                self.out.write(str(item))
                self.out.write(' ')
            self.out.write('\n')

        self.out.write('MetaVar ')
        self.out.write(str(id))
        write_list('eFresh', e_fresh)
        write_list('sFresh', s_fresh)
        write_list('pos', positive)
        write_list('neg', negative)
        write_list('appctx', application_context)

    @pretty()
    def implies(self, left: Pattern, right: Pattern) -> None:
        self.out.write('Implication')

    @pretty()
    def app(self, left: Pattern, right: Pattern) -> None:
        self.out.write('Application')

    @pretty()
    def exists(self, var: int, subpattern: Pattern) -> None:
        self.out.write('Exists ')
        self.out.write(str(var))

    @pretty()
    def mu(self, var: int, subpattern: Pattern) -> None:
        self.out.write('Mu ')
        self.out.write(str(var))

    @pretty()
    def esubst(self, evar_id: int, pattern: MetaVar | ESubst | SSubst, plug: Pattern) -> None:
        self.out.write(f'ESubst id={evar_id}')

    @pretty()
    def ssubst(self, svar_id: int, pattern: MetaVar | ESubst | SSubst, plug: Pattern) -> None:
        self.out.write(f'SSubst id={svar_id}')

    @pretty()
    def prop1(self) -> None:
        self.out.write('Prop1')

    @pretty()
    def prop2(self) -> None:
        self.out.write('Prop2')

    @pretty()
    def prop3(self) -> None:
        self.out.write('Prop3')

    @pretty()
    def modus_ponens(self, left: Proved, right: Proved) -> None:
        self.out.write('ModusPonens')

    @pretty()
    def instantiate(self, proved: Proved, delta: dict[int, Pattern]) -> None:
        self.out.write('Instantiate ')
        self.out.write(', '.join(map(str, delta.keys())))

    @pretty()
    def instantiate_notation(self, pattern: Pattern, delta: dict[int, Pattern]) -> None:
        self.out.write('Instantiate ')
        self.out.write(', '.join(map(str, delta.keys())))

    @pretty()
    def pop(self, term: Pattern | Proved) -> None:
        self.out.write('Pop')

    @pretty(print_stack=False)
    def save(self, id: str, term: Pattern | Proved) -> None:
        self.out.write('Save')

    @pretty()
    def load(self, id: str, term: Pattern | Proved) -> None:
        self.out.write('Load ')
        self.out.write(id)
        self.out.write('=')
        self.out.write(str(self.memory.index(term)))

    @pretty(print_stack=False)
    def publish_proof(self, proved: Proved) -> None:
        self.out.write('Publish')

    @pretty(print_stack=False)
    def publish_axiom(self, axiom: Pattern) -> None:
        self.out.write('Publish')

    @pretty(print_stack=False)
    def publish_claim(self, pattern: Pattern) -> None:
        self.out.write('Publish')

    def pretty_print_pattern(self, p: Pattern) -> str:
        if p in self.notation:
            return self.notation[p]

        # TODO: Figure out how to avoid this "double" definition of pretty printing for some cases
        # like implication while keeping notations
        match p:
            case Implication(left, right):
                return f'({self.pretty_print_pattern(left)} -> {self.pretty_print_pattern(right)})'
            case Application(left, right):
                return f'(app ({self.pretty_print_pattern(left)}) ({self.pretty_print_pattern(right)}))'
            case Exists(var, subpattern):
                return f'(\u2203 {str(var)} . {self.pretty_print_pattern(subpattern)})'
            case Mu(var, subpattern):
                return f'(\u03BC {self.pretty_print_pattern(var)} . {self.pretty_print_pattern(p.subpattern)})'
            case ESubst(pattern, var, plug):
                return f'({self.pretty_print_pattern(pattern)}[{self.pretty_print_pattern(plug)}/{str(var)}])'
            case SSubst(pattern, var, plug):
                return f'({self.pretty_print_pattern(pattern)}[{self.pretty_print_pattern(plug)}/{str(var)}])'
        return str(p)

    def print_stack(self) -> None:
        self.out.write('\tStack:\n')
        for i, item in enumerate(reversed(self.stack)):
            if isinstance(item, Proved):
                item = item.conclusion
            self.out.write(f'\t{i}: {self.pretty_print_pattern(item)}\n')


class NotationlessPrettyPrinter(PrettyPrintingInterpreter):
    def save(self, id: str, term: Pattern | Proved) -> None:
        id = str(len(self.memory))
        ret = super().save(id, term)
        return ret

    def load(self, id: str, term: Pattern | Proved) -> None:
        id = str(self.memory.index(term))
        ret = super().load(id, term)
        return ret


PatternExpression = Callable[[], Pattern]
ProvedExpression = Callable[[], Proved]


class ProofExp:
    interpreter: BasicInterpreter

    def __init__(self, interpreter: BasicInterpreter) -> None:
        self.interpreter = interpreter
        self.notation: dict[str, Pattern] = {}

    @staticmethod
    def axioms() -> list[Pattern]:
        raise NotImplementedError

    @staticmethod
    def claims() -> list[Pattern]:
        raise NotImplementedError

    def proof_expressions(self) -> list[ProvedExpression]:
        raise NotImplementedError

    # Patterns
    # ========

    def svar(self, id: int) -> Pattern:
        return self.interpreter.svar(id)

    def evar(self, id: int) -> Pattern:
        return self.interpreter.evar(id)

    def symbol(self, id: int) -> Pattern:
        return self.interpreter.symbol(id)

    def implies(self, left: Pattern, right: Pattern) -> Pattern:
        return self.interpreter.implies(left, right)

    def app(self, left: Pattern, right: Pattern) -> Pattern:
        return self.interpreter.app(left, right)

    def exists(self, var: int, subpattern: Pattern) -> Pattern:
        return self.interpreter.exists(var, subpattern)

    def mu(self, var: int, subpattern: Pattern) -> Pattern:
        return self.interpreter.mu(var, subpattern)

    def metavar(
        self,
        name: int,
        e_fresh: tuple[EVar, ...] = (),
        s_fresh: tuple[SVar, ...] = (),
        positive: tuple[SVar, ...] = (),
        negative: tuple[SVar, ...] = (),
        application_context: tuple[EVar, ...] = (),
    ) -> Pattern:
        return self.interpreter.metavar(name, e_fresh, s_fresh, positive, negative, application_context)

    # Proof Rules
    # -----------

    def prop1(self) -> Proved:
        return self.interpreter.prop1()

    def prop2(self) -> Proved:
        return self.interpreter.prop2()

    def prop3(self) -> Proved:
        return self.interpreter.prop3()

    def modus_ponens(self, left: Proved, right: Proved) -> Proved:
        return self.interpreter.modus_ponens(left, right)

    def dynamic_inst(self, proved_expr: ProvedExpression, delta: dict[int, Pattern]) -> Proved:
        for idn, p in delta.items():
            delta[idn] = self.interpreter.pattern(p)
        return self.interpreter.instantiate(proved_expr(), delta)

    def instantiate(self, proved: Proved, delta: dict[int, Pattern]) -> Proved:
        return self.interpreter.instantiate(proved, delta)

    def instantiate_notation(self, pattern: Pattern, delta: dict[int, Pattern]) -> Pattern:
        return self.interpreter.instantiate_notation(pattern, delta)

    def load_notation(self, id: str) -> Pattern | None:
        if id not in self.notation:
            return None
        ret = self.notation[id]
        self.interpreter.load(id, ret)
        return ret

    def load_axiom(self, axiom_term: Pattern) -> Proved:
        assert axiom_term in self.axioms()
        axiom = Proved(axiom_term)
        self.interpreter.load(f'Axiom {str(axiom)}', axiom)
        return axiom

    def save_notation(self, id: str, pattern: Pattern) -> Pattern:
        assert id not in self.notation
        self.notation[id] = pattern
        self.interpreter.save(id, pattern)
        return pattern

    def save_pattern(self, id: str, pattern: Pattern) -> Pattern:
        self.interpreter.save(id, pattern)
        return pattern

    def publish_axiom(self, proved: Pattern) -> Pattern:
        self.interpreter.publish_axiom(proved)
        return proved

    def publish_proof(self, proved: Proved) -> Proved:
        self.interpreter.publish_proof(proved)
        return proved

    def publish_claim(self, pattern: Pattern) -> Pattern:
        self.interpreter.publish_claim(pattern)
        return pattern

    def execute_gamma_phase(self) -> None:
        assert self.interpreter.phase == ExecutionPhase.Gamma
        for axiom in self.axioms():
            self.publish_axiom(self.interpreter.pattern(axiom))
        self.interpreter.into_claim_phase()

    def execute_claims_phase(self) -> None:
        assert self.interpreter.phase == ExecutionPhase.Claim
        for claim in reversed(self.claims()):
            self.publish_claim(self.interpreter.pattern(claim))
        self.interpreter.into_proof_phase()

    def execute_proofs_phase(self) -> None:
        assert self.interpreter.phase == ExecutionPhase.Proof
        for proof_expr in self.proof_expressions():
            self.publish_proof(proof_expr())

    def execute_full(self) -> None:
        assert self.interpreter.phase == ExecutionPhase.Gamma
        self.execute_gamma_phase()
        self.execute_claims_phase()
        self.execute_proofs_phase()

    @classmethod
    def serialize(cls, file_names: list[str]) -> None:
        prover = cls(
            interpreter=SerializingInterpreter(
                phase=ExecutionPhase.Gamma, out=open(file_names[0], 'wb'), claims=list(map(Claim, cls.claims()))
            )
        )

        assert isinstance(prover.interpreter, SerializingInterpreter)

        prover.execute_gamma_phase()
        # Execute gamma phase and change output file
        prover.interpreter.out.close()
        prover.interpreter.out = open(file_names[1], 'wb')

        # Execute claim phase and change output file
        prover.execute_claims_phase()
        prover.interpreter.out.close()
        prover.interpreter.out = open(file_names[2], 'wb')

        # Execute proof phase
        prover.execute_proofs_phase()
        prover.interpreter.out.close()

    @classmethod
    def prettyprint(cls, file_names: list[str]) -> None:
        prover = cls(
            PrettyPrintingInterpreter(
                phase=ExecutionPhase.Gamma, out=open(file_names[0], 'w'), claims=list(map(Claim, cls.claims()))
            )
        )

        assert isinstance(prover.interpreter, PrettyPrintingInterpreter)

        prover.execute_gamma_phase()
        # Execute gamma phase and change output file
        prover.interpreter.out.close()
        prover.interpreter.out = open(file_names[1], 'w')

        # Execute claim phase and change output file
        prover.execute_claims_phase()
        prover.interpreter.out.close()
        prover.interpreter.out = open(file_names[2], 'w')

        # Execute proof phase
        prover.execute_proofs_phase()
        prover.interpreter.out.close()

    @classmethod
    def memoize(cls, file_names: list[str]) -> None:
        counter = cls(
            CountingInterpreter(
                phase=ExecutionPhase.Gamma,
                claims=list(map(Claim, cls.claims())),
            )
        )

        assert isinstance(counter.interpreter, CountingInterpreter)
        counter.execute_full()

        memoizer = cls(
            MemoizingInterpreter(
                phase=ExecutionPhase.Gamma,
                claims=list(map(Claim, cls.claims())),
                out=open(file_names[0], 'wb'),
                patterns_for_memoization=counter.interpreter.finalize(),
            )
        )

        assert isinstance(memoizer.interpreter, MemoizingInterpreter)

        memoizer.execute_gamma_phase()
        memoizer.interpreter.out.close()
        memoizer.interpreter.out = open(file_names[1], 'wb')

        memoizer.execute_claims_phase()
        memoizer.interpreter.out.close()
        memoizer.interpreter.out = open(file_names[2], 'wb')

        memoizer.execute_proofs_phase()
        memoizer.interpreter.out.close()

    @classmethod
    def main(cls, argv: list[str]) -> None:
        exe, *argv = argv
        usage = f'Usage:\n\n python3 {exe} (binary|pretty) (claim|proof) output-file\n python3 {exe} --help\n\n'
        examples = (
            f'Examples:\n\npython3 {exe} binary claim a.out\n# outputs claims of ProofExp object in verifier-checkable binary format to file a.out\n\n'
            + f'python3 {exe} pretty claim /dev/stdout\n# outputs claims of ProofExp object in human-readable format to standard output\n'
        )

        if len(argv) == 1:
            assert argv[0] == '--help', usage
            print(usage + examples)
            return

        assert len(argv) == 3, usage
        format, mode, output_path = argv

        file_names = ['/dev/null', '/dev/null', '/dev/null']

        match mode:
            case 'gamma':
                file_names[0] = output_path
            case 'claim':
                file_names[1] = output_path
            case 'proof':
                file_names[2] = output_path

        match format:
            case 'pretty':
                cls.prettyprint(file_names)
            case 'binary':
                cls.serialize(file_names)
            case 'memo':
                cls.memoize(file_names)
