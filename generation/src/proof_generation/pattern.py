from __future__ import annotations

from dataclasses import dataclass


class Pattern:
    def instantiate(self, delta: dict[int, Pattern]) -> Pattern:
        raise NotImplementedError


@dataclass(frozen=True)
class EVar(Pattern):
    name: int

    def instantiate(self, delta: dict[int, Pattern]) -> Pattern:
        return self

    def __str__(self) -> str:
        return f'x{self.name}'


@dataclass(frozen=True)
class SVar(Pattern):
    name: int

    def instantiate(self, delta: dict[int, Pattern]) -> Pattern:
        return self

    def __str__(self) -> str:
        return f'X{self.name}'


@dataclass(frozen=True)
class Symbol(Pattern):
    name: int

    def instantiate(self, delta: dict[int, Pattern]) -> Pattern:
        return self

    def __str__(self) -> str:
        return str(self.name)


@dataclass(frozen=True)
class Implication(Pattern):
    left: Pattern
    right: Pattern

    def instantiate(self, delta: dict[int, Pattern]) -> Pattern:
        return Implication(self.left.instantiate(delta), self.right.instantiate(delta))

    def __str__(self) -> str:
        return f'({str(self.left)} -> {str(self.right)})'


@dataclass(frozen=True)
class Application(Pattern):
    left: Pattern
    right: Pattern

    def instantiate(self, delta: dict[int, Pattern]) -> Pattern:
        return Application(self.left.instantiate(delta), self.right.instantiate(delta))

    def __str__(self) -> str:
        return f'(app ({str(self.left)}) ({str(self.right)}))'


@dataclass(frozen=True)
class Exists(Pattern):
    var: EVar
    subpattern: Pattern

    def instantiate(self, delta: dict[int, Pattern]) -> Pattern:
        return Exists(self.var, self.subpattern.instantiate(delta))

    def __str__(self) -> str:
        return f'(\u2203 {str(self.var)} . {str(self.subpattern)})'


@dataclass(frozen=True)
class Mu(Pattern):
    var: SVar
    subpattern: Pattern

    def instantiate(self, delta: dict[int, Pattern]) -> Pattern:
        return Mu(self.var, self.subpattern.instantiate(delta))

    def __str__(self) -> str:
        return f'(\u03BC {str(self.var)} . {str(self.subpattern)})'


@dataclass(frozen=True)
class MetaVar(Pattern):
    name: int
    e_fresh: tuple[EVar, ...] = ()
    s_fresh: tuple[SVar, ...] = ()
    positive: tuple[SVar, ...] = ()
    negative: tuple[SVar, ...] = ()
    app_ctx_holes: tuple[EVar, ...] = ()

    def instantiate(self, delta: dict[int, Pattern]) -> Pattern:
        if self.name in delta:
            return delta[self.name]
        return self

    def __str__(self) -> str:
        return f'phi{self.name}'


@dataclass(frozen=True)
class ESubst(Pattern):
    pattern: MetaVar
    var: EVar
    plug: Pattern

    def __str__(self) -> str:
        return f'({str(self.pattern)}[{str(self.plug)}/{str(self.var)}])'


@dataclass(frozen=True)
class SSubst(Pattern):
    pattern: MetaVar
    var: SVar
    plug: Pattern

    def __str__(self) -> str:
        return f'({str(self.pattern)}[{str(self.plug)}/{str(self.var)}])'
