from __future__ import annotations

from dataclasses import dataclass, field


class Pattern:
    def instantiate(self, delta: dict[int, Pattern]) -> Pattern:
        raise NotImplementedError

    def apply_esubst(self, evar_id: int, plug: Pattern) -> Pattern:
        raise NotImplementedError

    def apply_ssubst(self, svar_id: int, plug: Pattern) -> Pattern:
        raise NotImplementedError


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

    def __str__(self) -> str:
        return f'X{self.name}'


@dataclass(frozen=True)
class Symbol(Pattern):
    name: int
    pretty_name: str | None = field(default=None, compare=False)

    def instantiate(self, delta: dict[int, Pattern]) -> Pattern:
        return self

    def apply_esubst(self, evar_id: int, plug: Pattern) -> Pattern:
        return self

    def apply_ssubst(self, svar_id: int, plug: Pattern) -> Pattern:
        return self

    def __str__(self) -> str:
        if self.pretty_name is None:
            return f'σ{str(self.name)}'
        else:
            return f'{self.pretty_name}_{str(self.name)}'


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

    def instantiate(self, delta: dict[int, Pattern]) -> Pattern:
        if self.name in delta:
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


InstantiationDict = dict[int, Pattern]


@dataclass(frozen=True)
class Instantiate(Pattern):
    """Constructor for an unsimplified Instantiated Pattern.
    This is typically used to contain Notation.
    """

    pattern: Pattern
    inst: InstantiationDict

    def simplify(self) -> Pattern:
        """Instantiate pattern with plug.
        Note that this doesn't fully reduce all notation, just one level.
        """
        return self.pattern.instantiate(self.inst)

    def __eq__(self, o: object) -> bool:
        # TODO: This should recursively remove all notation.
        return self.simplify() == o

    def instantiate(self, delta: dict[int, Pattern]) -> Pattern:
        instantiated_subst = {k: v.instantiate(delta) for k, v in self.inst.items()}
        unshadowed_delta = {k: v for k, v in delta.items() if k not in self.inst}
        return Instantiate(self.pattern.instantiate(unshadowed_delta), instantiated_subst)

    def apply_esubst(self, evar_id: int, plug: Pattern) -> Pattern:
        inst = {k: v.apply_esubst(evar_id, plug) for k, v in self.inst.items()}
        return Instantiate(self.pattern.apply_esubst(evar_id, plug), inst)

    def apply_ssubst(self, svar_id: int, plug: Pattern) -> Pattern:
        inst = {k: v.apply_ssubst(svar_id, plug) for k, v in self.inst.items()}
        return Instantiate(self.pattern.apply_ssubst(svar_id, plug), inst)


@dataclass(frozen=True)
class Notation:
    label: str
    definition: Pattern
    format_str: str

    def __call__(self, *args: Pattern) -> Pattern:
        return Instantiate(self.definition, dict(enumerate(args)))


# @dataclass(frozen=True, eq=False)
# class FakeNotation(Notation):
#     symbol: Symbol
#     pattern_arguments: tuple[Pattern, ...]
#
#     def label(self) -> str:
#         return f'FakeNotation[{str(self.symbol)}]'
#
#     def definition(self) -> Pattern:
#         if len(self.pattern_arguments) == 0:
#             return self.symbol
#         else:
#             current_callable: Pattern = self.symbol
#             arguments_left = [MetaVar(i) for i, _ in enumerate(self.pattern_arguments)]
#             while len(arguments_left) > 0:
#                 next_one, *arguments_left = arguments_left
#                 current_callable = App(current_callable, next_one)
#             return current_callable
#
#     def arguments(self) -> dict[int, Pattern]:
#         ret: dict[int, Pattern] = {}
#
#         for i, arg in enumerate(self.pattern_arguments):
#             ret[i] = arg
#
#         return ret
#
#     def instantiate(self, delta: dict[int, Pattern]) -> Pattern:
#         args = self._instantiate_args(delta)
#         return FakeNotation(self.symbol, tuple(args))


bot = Notation('bot', Mu(0, SVar(0)), '⊥')
