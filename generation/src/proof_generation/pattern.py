from __future__ import annotations

from abc import ABC
from dataclasses import dataclass


def match_single(
    pattern: Pattern, instance: Pattern, extend: dict[int, Pattern] | None = None
) -> dict[int, Pattern] | None:
    ret: dict[int, Pattern] | None
    ret = extend if extend else {}

    if isinstance(pattern, MetaVar):
        id = pattern.name
        if id in ret:
            if ret[id] != instance:
                return None
        else:
            if not pattern.can_be_replaced_by(instance):
                return None
            ret[id] = instance
    elif (pat_imp := Implies.unwrap(pattern)) and (inst_imp := Implies.unwrap(instance)):
        ret = match_single(pat_imp[0], inst_imp[0], ret)
        if not ret:
            return None
        ret = match_single(pat_imp[1], inst_imp[1], ret)
    elif (pat_evar := EVar.deconstruct(pattern)) and (inst_evar := EVar.deconstruct(instance)):
        if pat_evar != inst_evar:
            return None
    elif (pat_svar := SVar.deconstruct(pattern)) and (inst_svar := SVar.deconstruct(instance)):
        if pat_svar != inst_svar:
            return None
    elif (pat_sym := Symbol.deconstruct(pattern)) and (inst_sym := Symbol.deconstruct(instance)):
        if pat_sym != inst_sym:
            return None
    elif (pat_app := App.unwrap(pattern)) and (inst_app := App.unwrap(instance)):
        ret = match_single(pat_app[0], inst_app[0], ret)
        if not ret:
            return None
        ret = match_single(pat_app[1], inst_app[1], ret)
    elif (pat_ex := Exists.deconstruct(pattern)) and (inst_ex := Exists.deconstruct(instance)):
        if pat_ex[0] != inst_ex[0]:
            return None
        ret = match_single(pat_ex[1], inst_ex[1], ret)
    elif (pat_mu := Mu.deconstruct(pattern)) and (inst_mu := Mu.deconstruct(instance)):
        if pat_mu[0] != inst_mu[0]:
            return None
        ret = match_single(pat_mu[1], inst_mu[1], ret)
    # TODO Consider adding cases for ESubst/SSubst
    else:
        return None
    return ret


def match(equations: list[tuple[Pattern, Pattern]]) -> dict[int, Pattern] | None:
    ret: dict[int, Pattern] = {}
    for pattern, instance in equations:
        submatch = match_single(pattern, instance, ret)
        if not submatch:
            return None
        ret = submatch
    return ret


class Pattern:
    def ef(self, name: int) -> bool:
        raise NotImplementedError

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

    def ef(self, name: int) -> bool:
        return name != self.name

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

    def ef(self, name: int) -> bool:
        return True

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

    def ef(self, name: int) -> bool:
        return True

    def instantiate(self, delta: dict[int, Pattern]) -> Pattern:
        return self

    def apply_esubst(self, evar_id: int, plug: Pattern) -> Pattern:
        return self

    def apply_ssubst(self, svar_id: int, plug: Pattern) -> Pattern:
        return self

    @staticmethod
    def deconstruct(pat: Pattern) -> str | None:
        if isinstance(pat, Symbol):
            return pat.name
        if isinstance(pat, Notation):
            return Symbol.deconstruct(pat.conclusion())
        return None

    def __str__(self) -> str:
        return f'\u03c3{self.name}'


@dataclass(frozen=True)
class Implies(Pattern):
    left: Pattern
    right: Pattern

    def ef(self, name: int) -> bool:
        return self.left.ef(name) and self.right.ef(name)

    def instantiate(self, delta: dict[int, Pattern]) -> Pattern:
        return Implies(self.left.instantiate(delta), self.right.instantiate(delta))

    def apply_esubst(self, evar_id: int, plug: Pattern) -> Pattern:
        return Implies(self.left.apply_esubst(evar_id, plug), self.right.apply_esubst(evar_id, plug))

    def apply_ssubst(self, svar_id: int, plug: Pattern) -> Pattern:
        return Implies(self.left.apply_ssubst(svar_id, plug), self.right.apply_ssubst(svar_id, plug))

    def __str__(self) -> str:
        return f'({str(self.left)} -> {str(self.right)})'


def imp(p1: Pattern, p2: Pattern) -> Pattern:
    return Implies(p1, p2)


@dataclass(frozen=True)
class App(Pattern):
    left: Pattern
    right: Pattern

    def ef(self, name: int) -> bool:
        return self.left.ef(name) and self.right.ef(name)

    def instantiate(self, delta: dict[int, Pattern]) -> Pattern:
        return App(self.left.instantiate(delta), self.right.instantiate(delta))

    def apply_esubst(self, evar_id: int, plug: Pattern) -> Pattern:
        return App(self.left.apply_esubst(evar_id, plug), self.right.apply_esubst(evar_id, plug))

    def apply_ssubst(self, svar_id: int, plug: Pattern) -> Pattern:
        return App(self.left.apply_ssubst(svar_id, plug), self.right.apply_ssubst(svar_id, plug))

    def __str__(self) -> str:
        return f'app({str(self.left)}, {str(self.right)})'


@dataclass(frozen=True)
class Exists(Pattern):
    var: int
    subpattern: Pattern

    def ef(self, name: int) -> bool:
        return name == self.var or self.subpattern.ef(name)

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

    def ef(self, name: int) -> bool:
        return self.subpattern.ef(name)

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

    def ef(self, name: int) -> bool:
        return name in self.e_fresh

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

    def ef(self, name: int) -> bool:
        if self.var == name:
            return self.plug.ef(name)

        # We assume that at least one instance will be replaced
        return self.pattern.ef(name) and self.plug.ef(name)

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

    def ef(self, name: int) -> bool:
        # We assume that at least one instance will be replaced
        return self.pattern.ef(name) and self.plug.ef(name)

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

    # All subclasses of Notation MUST implement one of the two methods below
    @classmethod
    def definition(cls) -> Pattern:
        return cls().object_definition()

    def object_definition(self) -> Pattern:
        return type(self).definition()

    def conclusion(self) -> Pattern:
        return self.object_definition().instantiate(self._arguments())

    def ef(self, name: int) -> bool:
        return self.conclusion().ef(name)

    # We assume all metavars in notations are instantiated for
    # So this is correct, as this can only change "internals" of the instantiations
    def instantiate(self, delta: dict[int, Pattern]) -> Pattern:
        pattern_args = self._instantiate_args(delta)

        final_args = []
        for arg in vars(self).values():
            if isinstance(arg, Pattern):
                final_args.append(pattern_args.pop(0))
            else:
                final_args.append(arg)

        return type(self)(*final_args)

    # TODO: Keep notations (without dropping them)
    def apply_esubst(self, evar_id: int, plug: Pattern) -> Pattern:
        return self.conclusion().apply_esubst(evar_id, plug)

    # TODO: Keep notations (without dropping them)
    def apply_ssubst(self, svar_id: int, plug: Pattern) -> Pattern:
        return self.conclusion().apply_ssubst(svar_id, plug)

    @classmethod
    def unwrap(cls, pattern: Pattern) -> tuple[Pattern, ...] | None:
        assert cls is not Notation
        assert issubclass(cls, Notation)
        if isinstance(pattern, cls):
            return tuple([v for _, v in sorted(pattern._arguments().items())])
        match_result = match_single(cls.definition(), pattern)
        if match_result is None:
            return None
        return tuple([v for _, v in sorted(match_result.items())])

    def _arguments(self) -> dict[int, Pattern]:
        ret: dict[int, Pattern] = {}

        i = 0
        for arg in vars(self).values():
            if isinstance(arg, Pattern):
                ret[i] = arg
                i += 1

        return ret

    def _instantiate_args(self, delta: dict[int, Pattern]) -> list[Pattern]:
        args: list[Pattern] = []

        for arg in self._arguments().values():
            args.append(arg.instantiate(delta))

        return args

    def __eq__(self, o: object) -> bool:
        assert isinstance(o, Pattern)
        if isinstance(o, Notation) and type(o) == type(self):
            return o._arguments() == self._arguments()
        return self.conclusion() == o

    def __str__(self) -> str:
        pretty_args = ', '.join(map(str, self._arguments().values()))
        return f'{self.label()} ({pretty_args})'


@dataclass(frozen=True, eq=False)
class NotationPlaceholder(Notation):
    symbol: Symbol
    pattern_arguments: tuple[Pattern, ...]

    def label(self) -> str:
        return f'{type(self).__name__}[{str(self.symbol)}]'

    def object_definition(self) -> Pattern:
        if len(self.pattern_arguments) == 0:
            return self.symbol
        else:
            current_callable: Pattern = self.symbol
            arguments_left = [MetaVar(i) for i, _ in enumerate(self.pattern_arguments)]
            while len(arguments_left) > 0:
                next_one, *arguments_left = arguments_left
                current_callable = App(current_callable, next_one)
            return current_callable

    def instantiate(self, delta: dict[int, Pattern]) -> Pattern:
        args = self._instantiate_args(delta)
        return NotationPlaceholder(self.symbol, tuple(args))

    def _arguments(self) -> dict[int, Pattern]:
        ret: dict[int, Pattern] = {}

        for i, arg in enumerate(self.pattern_arguments):
            ret[i] = arg

        return ret

    def __eq__(self, o: object) -> bool:
        assert isinstance(o, Pattern)
        if isinstance(o, Notation) and type(o) == type(self):
            return o._arguments() == self._arguments()
        return self.conclusion() == o


@dataclass(frozen=True, eq=False)
class Bot(Notation):
    @classmethod
    def definition(cls) -> Pattern:
        return Mu(0, SVar(0))

    def __str__(self) -> str:
        return '⊥'


bot = Bot()
