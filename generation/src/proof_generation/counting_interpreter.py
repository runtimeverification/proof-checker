from __future__ import annotations

from collections import namedtuple
from typing import TYPE_CHECKING

from proof_generation.pattern import Application, Exists, Implication, Mu
from proof_generation.proved import Proved
from proof_generation.stateful_interpreter import StatefulInterpreter

if TYPE_CHECKING:
    from proof_generation.basic_interpreter import ExecutionPhase
    from proof_generation.claim import Claim
    from proof_generation.pattern import ESubst, EVar, MetaVar, Pattern, SSubst, SVar


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
