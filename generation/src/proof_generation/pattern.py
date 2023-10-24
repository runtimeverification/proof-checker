from __future__ import annotations

from abc import ABC, abstractmethod
from dataclasses import dataclass


class Pattern:
    def instantiate(self, delta: dict[int, Pattern]) -> Pattern:
        raise NotImplementedError

    def apply_esubst(self, evar_id: int, plug: Pattern) -> Pattern:
        raise NotImplementedError

    def apply_ssubst(self, svar_id: int, plug: Pattern) -> Pattern:
        raise NotImplementedError

    @classmethod
    def unwrap(cls, pattern: Pattern) -> tuple[Pattern, ...] | None:
        if isinstance(pattern, Notation):
            return cls.unwrap(pattern.conclusion())
        if isinstance(pattern, cls):
            return tuple([v for _, v in sorted(vars(pattern).items()) if isinstance(v, Pattern)])
        return None

    @classmethod
    def extract(cls, pattern: Pattern) -> tuple[Pattern, ...]:
        ret = cls.unwrap(pattern)
        assert ret is not None, f'Expected a/an {cls.__name__} but got instead: {str(pattern)}\n'
        return ret

    def __eq__(self, o: object) -> bool:
        if isinstance(o, Notation):
            return self.__eq__(o.conclusion())
        return False


@dataclass(frozen=True)
class EVar(Pattern):
    name: int

    def instantiate(self, delta: dict[int, Pattern]) -> Pattern:
        return self

    def apply_esubst(self, evar_id: int, plug: Pattern) -> Pattern:
        if evar_id == self.name:
            return plug
        return self

    def apply_ssubst(self, svar_id: int, plug: Pattern) -> Pattern:
        return self

    @staticmethod
    def deconstruct(pat: Pattern) -> int | None:
        if isinstance(pat, EVar):
            return pat.name
        if isinstance(pat, Notation):
            return EVar.deconstruct(pat.conclusion())
        return None

    def __str__(self) -> str:
        return f'x{self.name}'


@dataclass(frozen=True)
class SVar(Pattern):
    name: int

    def instantiate(self, delta: dict[int, Pattern]) -> Pattern:
        return self

    def apply_esubst(self, evar_id: int, plug: Pattern) -> Pattern:
        return self

    def apply_ssubst(self, svar_id: int, plug: Pattern) -> Pattern:
        if svar_id == self.name:
            return plug
        return self

    @staticmethod
    def deconstruct(pat: Pattern) -> int | None:
        if isinstance(pat, SVar):
            return pat.name
        if isinstance(pat, Notation):
            return SVar.deconstruct(pat.conclusion())
        return None

    def __str__(self) -> str:
        return f'X{self.name}'


@dataclass(frozen=True)
class Symbol(Pattern):
    name: str

    def instantiate(self, delta: dict[int, Pattern]) -> Pattern:
        return self

    def apply_esubst(self, evar_id: int, plug: Pattern) -> Pattern:
        return self

    def apply_ssubst(self, svar_id: int, plug: Pattern) -> Pattern:
        return self

    def __str__(self) -> str:
        return f'\u03c3{self.name}'


@dataclass(frozen=True)
class Implies(Pattern):
    left: Pattern
    right: Pattern

    def instantiate(self, delta: dict[int, Pattern]) -> Pattern:
        return Implies(self.left.instantiate(delta), self.right.instantiate(delta))

    def apply_esubst(self, evar_id: int, plug: Pattern) -> Pattern:
        return Implies(self.left.apply_esubst(evar_id, plug), self.right.apply_esubst(evar_id, plug))

    def apply_ssubst(self, svar_id: int, plug: Pattern) -> Pattern:
        return Implies(self.left.apply_ssubst(svar_id, plug), self.right.apply_ssubst(svar_id, plug))

    def __str__(self) -> str:
        return f'({str(self.left)} -> {str(self.right)})'


@dataclass(frozen=True)
class App(Pattern):
    left: Pattern
    right: Pattern

    def instantiate(self, delta: dict[int, Pattern]) -> Pattern:
        return App(self.left.instantiate(delta), self.right.instantiate(delta))

    def apply_esubst(self, evar_id: int, plug: Pattern) -> Pattern:
        return App(self.left.apply_esubst(evar_id, plug), self.right.apply_esubst(evar_id, plug))

    def apply_ssubst(self, svar_id: int, plug: Pattern) -> Pattern:
        return App(self.left.apply_ssubst(svar_id, plug), self.right.apply_ssubst(svar_id, plug))

    def __str__(self) -> str:
        return f'(app ({str(self.left)}) ({str(self.right)}))'


@dataclass(frozen=True)
class Exists(Pattern):
    var: int
    subpattern: Pattern

    def instantiate(self, delta: dict[int, Pattern]) -> Pattern:
        return Exists(self.var, self.subpattern.instantiate(delta))

    def apply_esubst(self, evar_id: int, plug: Pattern) -> Pattern:
        if evar_id == self.var:
            return self
        return Exists(self.var, self.subpattern.apply_esubst(evar_id, plug))

    def apply_ssubst(self, svar_id: int, plug: Pattern) -> Pattern:
        return Exists(self.var, self.subpattern.apply_ssubst(svar_id, plug))

    @staticmethod
    def deconstruct(pat: Pattern) -> tuple[int, Pattern] | None:
        if isinstance(pat, Exists):
            return pat.var, pat.subpattern
        if isinstance(pat, Notation):
            return Exists.deconstruct(pat.conclusion())
        return None

    def __str__(self) -> str:
        return f'(∃ x{self.var} . {str(self.subpattern)})'


@dataclass(frozen=True)
class Mu(Pattern):
    var: int
    subpattern: Pattern

    def instantiate(self, delta: dict[int, Pattern]) -> Pattern:
        return Mu(self.var, self.subpattern.instantiate(delta))

    def apply_esubst(self, evar_id: int, plug: Pattern) -> Pattern:
        return Mu(self.var, self.subpattern.apply_esubst(evar_id, plug))

    def apply_ssubst(self, svar_id: int, plug: Pattern) -> Pattern:
        if svar_id == self.var:
            return self
        return Mu(self.var, self.subpattern.apply_ssubst(svar_id, plug))

    @staticmethod
    def deconstruct(pat: Pattern) -> tuple[int, Pattern] | None:
        if isinstance(pat, Mu):
            return pat.var, pat.subpattern
        if isinstance(pat, Notation):
            return Mu.deconstruct(pat.conclusion())
        return None

    def __str__(self) -> str:
        return f'(μ X{self.var} . {str(self.subpattern)})'


@dataclass(frozen=True)
class MetaVar(Pattern):
    name: int
    e_fresh: tuple[EVar, ...] = ()
    s_fresh: tuple[SVar, ...] = ()
    positive: tuple[SVar, ...] = ()
    negative: tuple[SVar, ...] = ()
    app_ctx_holes: tuple[EVar, ...] = ()

    def can_be_replaced_by(self, pat: Pattern) -> bool:
        # TODO implement this function by checking constraints
        return True

    def instantiate(self, delta: dict[int, Pattern]) -> Pattern:
        if self.name in delta:
            assert self.can_be_replaced_by(
                delta[self.name]
            ), f'Invalid instantiation when trying to instantiate {str(self)} with {str(delta[self.name])}\n'
            return delta[self.name]
        return self

    def apply_esubst(self, evar_id: int, plug: Pattern) -> Pattern:
        if EVar(evar_id) in self.e_fresh:
            return self
        return ESubst(pattern=self, var=EVar(evar_id), plug=plug)

    def apply_ssubst(self, svar_id: int, plug: Pattern) -> Pattern:
        if SVar(svar_id) in self.s_fresh:
            return self
        return SSubst(pattern=self, var=SVar(svar_id), plug=plug)

    def __str__(self) -> str:
        return f'phi{self.name}'


@dataclass(frozen=True)
class ESubst(Pattern):
    pattern: MetaVar | ESubst | SSubst
    var: EVar
    plug: Pattern

    def instantiate(self, delta: dict[int, Pattern]) -> Pattern:
        return self.pattern.instantiate(delta).apply_esubst(self.var.name, self.plug.instantiate(delta))

    def apply_esubst(self, evar_id: int, plug: Pattern) -> Pattern:
        return ESubst(pattern=self, var=EVar(evar_id), plug=plug)

    def apply_ssubst(self, svar_id: int, plug: Pattern) -> Pattern:
        return SSubst(pattern=self, var=SVar(svar_id), plug=plug)

    def __str__(self) -> str:
        return f'({str(self.pattern)}[{str(self.plug)}/{str(self.var)}])'


@dataclass(frozen=True)
class SSubst(Pattern):
    pattern: MetaVar | ESubst | SSubst
    var: SVar
    plug: Pattern

    def instantiate(self, delta: dict[int, Pattern]) -> Pattern:
        return self.pattern.instantiate(delta).apply_ssubst(self.var.name, self.plug.instantiate(delta))

    def apply_esubst(self, evar_id: int, plug: Pattern) -> Pattern:
        return ESubst(pattern=self, var=EVar(evar_id), plug=plug)

    def apply_ssubst(self, svar_id: int, plug: Pattern) -> Pattern:
        return SSubst(pattern=self, var=SVar(svar_id), plug=plug)

    def __str__(self) -> str:
        return f'({str(self.pattern)}[{str(self.plug)}/{str(self.var)}])'


@dataclass(frozen=True)
class Notation(Pattern, ABC):
    def label(self) -> str:
        return f'{type(self).__name__!r}'

    @abstractmethod
    def definition(self) -> Pattern:
        raise NotImplementedError('This notation has no definition.')

    def arguments(self) -> dict[int, Pattern]:
        ret: dict[int, Pattern] = {}

        for i, arg in enumerate(vars(self).values()):
            assert isinstance(arg, Pattern)
            ret[i] = arg

        return ret

    def conclusion(self) -> Pattern:
        return self.definition().instantiate(self.arguments())

    # We assume all metavars in notations are instantiated for
    # So this is correct, as this can only change "internals" of the instantiations
    def instantiate(self, delta: dict[int, Pattern]) -> Pattern:
        args = self.instantiate(delta)
        return type(self)(*args)

    # TODO: Keep notations (without dropping them)
    def apply_esubst(self, evar_id: int, plug: Pattern) -> Pattern:
        return self.conclusion().apply_esubst(evar_id, plug)

    # TODO: Keep notations (without dropping them)
    def apply_ssubst(self, svar_id: int, plug: Pattern) -> Pattern:
        return self.conclusion().apply_ssubst(svar_id, plug)

    def __str__(self) -> str:
        pretty_args = ', '.join(map(str, self.arguments().values()))
        return f'{self.label()} ({pretty_args})'


@dataclass(frozen=True, eq=False)
class FakeNotation(Notation):
    symbol: Symbol
    pattern_arguments: tuple[Pattern, ...]

    def label(self) -> str:
        return f'FakeNotation[{str(self.symbol)}]'

    def definition(self) -> Pattern:
        if len(self.pattern_arguments) == 0:
            return self.symbol
        else:
            current_callable: Pattern = self.symbol
            arguments_left = [MetaVar(i) for i, _ in enumerate(self.pattern_arguments)]
            while len(arguments_left) > 0:
                next_one, *arguments_left = arguments_left
                current_callable = App(current_callable, next_one)
            return current_callable

    def arguments(self) -> dict[int, Pattern]:
        ret: dict[int, Pattern] = {}

        for i, arg in enumerate(self.pattern_arguments):
            ret[i] = arg

        return ret

    def instantiate(self, delta: dict[int, Pattern]) -> Pattern:
        args = self.instantiate(delta)
        return FakeNotation(self.symbol, tuple(args))

    def __eq__(self, o: object) -> bool:
        assert isinstance(o, Pattern)
        if isinstance(o, Notation) and type(o) == type(self):
            return o.arguments() == self.arguments()
        return self.conclusion() == o


@dataclass(frozen=True, eq=False)
class Bot(Notation):
    def definition(self) -> Pattern:
        return Mu(0, SVar(0))

    def __str__(self) -> str:
        return '⊥'


bot = Bot()
