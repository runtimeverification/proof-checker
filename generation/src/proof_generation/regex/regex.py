from __future__ import annotations

from dataclasses import dataclass


@dataclass(frozen=True)
class Regex:
    pass


@dataclass(frozen=True, order=True)
class EmptySet(Regex):
    def __str__(self):
        return 'empty'


@dataclass(frozen=True, order=True)
class Epsilon(Regex):
    def __str__(self):
        return 'epsilon'


@dataclass(frozen=True, order=True)
class Letter(Regex):
    name: str

    def __str__(self):
        return self.name


a = Letter('a')
b = Letter('b')


@dataclass(frozen=True, order=True)
class Concat(Regex):
    left: Regex
    right: Regex

    def __str__(self):
        return '[' + str(self.left) + ' ' + str(self.right) + ']'


@dataclass(frozen=True, order=True)
class Choice(Regex):
    left: Regex
    right: Regex

    def __str__(self):
        match self.left:
            case Not(l):
                return '(' + str(l) + ' -> ' + str(self.right) + ')'
            case _:
                return '(' + str(self.left) + ' + ' + str(self.right) + ')'


@dataclass(frozen=True, order=True)
class Kleene(Regex):
    exp: Regex

    def __str__(self):
        return '(' + str(self.exp) + ')*'


@dataclass(frozen=True, order=True)
class Not(Regex):
    exp: Regex

    def __str__(self):
        return '~' + str(self.exp)


def implies(l: Regex, r: Regex) -> Regex:
    return Choice(Not(l), r)


regex_types = [
    EmptySet,
    Epsilon,
    Letter,
    Concat,
    Choice,
    Kleene,
    Not,
]


def less_than(e1: Regex, e2: Regex) -> bool:
    t1 = type(e1)
    t2 = type(e2)
    assert t1 in regex_types
    assert t2 in regex_types
    if t1 == t2:
        return e1 < e2  # type: ignore
    return regex_types.index(t1) < regex_types.index(t2)
