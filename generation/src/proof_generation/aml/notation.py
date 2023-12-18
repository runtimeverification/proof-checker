from __future__ import annotations

from dataclasses import dataclass
from typing import TYPE_CHECKING

from frozendict import frozendict

from .syntax import Implies, Instantiate, MetaVar, Mu, Pattern, PrettyOptions, SVar, phi0, phi1
from .matching import match_single

if TYPE_CHECKING:
    pass


@dataclass(frozen=True)
class Notation:
    label: str
    arity: int
    definition: Pattern
    format_str: str

    def __post_init__(self) -> None:
        if self.definition.metavars():
            assert (
                max(self.definition.metavars()) < self.arity
            ), f'Notation {self.label}: Number of variables used is greater than Arity.'

        assert self.definition.occurring_vars() == set()

    def __call__(self, *args: Pattern) -> Pattern:
        assert len(args) == self.arity, f'Notation {self.label}: expected {self.arity} arguements, got {len(args)}.'
        return Instantiate(self.definition, frozendict(enumerate(args)))

    def matches(self, pattern: Pattern) -> None | tuple[Pattern, ...]:
        match = match_single(self.definition, pattern)
        if match is None:
            return None
        return tuple((match[i] if i in match else MetaVar(i)) for i in range(self.arity))

    def assert_matches(self, pattern: Pattern) -> tuple[Pattern, ...]:
        if match := self.matches(pattern):
            return match
        raise AssertionError(f'Does not match notation {self.label}: {str(pattern)}')

    def print_instantiation(self, applied: Instantiate, opts: PrettyOptions) -> str:
        assert applied.pattern == self.definition
        pretty_opts = [p.pretty(opts) for _, p in sorted(applied.inst.items())]
        try:
            return self.format_str.format(*pretty_opts)
        except Exception as e:
            raise ValueError(f'Cannot format malformed notation {self.label}: {self.format_str}') from e


bot = Notation('bot', 0, Mu(0, SVar(0)), '⊥')
neg = Notation('not', 1, Implies(MetaVar(0), bot()), '¬{0}')
top = Notation('top', 0, neg(bot()), '⊤')
_and = Notation('and', 2, neg(Implies(phi0, neg(phi1))), '({0} ⋀ {1})')
_or = Notation('or', 2, Implies(neg(phi0), phi1), '({0} ⋁ {1})')
equiv = Notation('equiv', 2, _and(Implies(phi0, phi1), Implies(phi1, phi0)), f'({0} <-> {1})')
