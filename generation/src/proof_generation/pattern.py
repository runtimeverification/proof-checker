from __future__ import annotations

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
    elif pattern == bot and instance == bot:
        pass
    elif (pat_imp := Implication.unwrap(pattern)) and (inst_imp := Implication.unwrap(instance)):
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
    elif (pat_app := Application.unwrap(pattern)) and (inst_app := Application.unwrap(instance)):
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
    name: int

    def instantiate(self, delta: dict[int, Pattern]) -> Pattern:
        return self

    def apply_esubst(self, evar_id: int, plug: Pattern) -> Pattern:
        return self

    def apply_ssubst(self, svar_id: int, plug: Pattern) -> Pattern:
        return self

    @staticmethod
    def deconstruct(pat: Pattern) -> int | None:
        if isinstance(pat, Symbol):
            return pat.name
        if isinstance(pat, Notation):
            return Symbol.deconstruct(pat.conclusion())
        return None

    def __str__(self) -> str:
        return f'\u03c3{str(self.name)}'


@dataclass(frozen=True)
class Implication(Pattern):
    left: Pattern
    right: Pattern

    def instantiate(self, delta: dict[int, Pattern]) -> Pattern:
        return Implication(self.left.instantiate(delta), self.right.instantiate(delta))

    def apply_esubst(self, evar_id: int, plug: Pattern) -> Pattern:
        return Implication(self.left.apply_esubst(evar_id, plug), self.right.apply_esubst(evar_id, plug))

    def apply_ssubst(self, svar_id: int, plug: Pattern) -> Pattern:
        return Implication(self.left.apply_ssubst(svar_id, plug), self.right.apply_ssubst(svar_id, plug))

    def __str__(self) -> str:
        return f'({str(self.left)} -> {str(self.right)})'


def imp(p1: Pattern, p2: Pattern) -> Pattern:
    return Implication(p1, p2)


@dataclass(frozen=True)
class Application(Pattern):
    left: Pattern
    right: Pattern

    def instantiate(self, delta: dict[int, Pattern]) -> Pattern:
        return Application(self.left.instantiate(delta), self.right.instantiate(delta))

    def apply_esubst(self, evar_id: int, plug: Pattern) -> Pattern:
        return Application(self.left.apply_esubst(evar_id, plug), self.right.apply_esubst(evar_id, plug))

    def apply_ssubst(self, svar_id: int, plug: Pattern) -> Pattern:
        return Application(self.left.apply_ssubst(svar_id, plug), self.right.apply_ssubst(svar_id, plug))


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
        return f'(\u2203 x{self.var} . {str(self.subpattern)})'


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
        return f'(\u03BC X{self.var} . {str(self.subpattern)})'


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
class Notation(Pattern):
    @classmethod
    def label(cls) -> str:
        return f'{cls.__name__!r}'

    @staticmethod
    def definition() -> Pattern:
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
        args: list[Pattern] = []

        for arg in self.arguments().values():
            args.append(arg.instantiate(delta))

        return type(self)(*args)

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
            return tuple([v for _, v in sorted(pattern.arguments().items())])
        match_result = match_single(cls.definition(), pattern)
        if match_result is None:
            return None
        return tuple([v for _, v in sorted(match_result.items())])

    @classmethod
    def extract(cls, pattern: Pattern) -> tuple[Pattern, ...]:
        ret = cls.unwrap(pattern)
        assert ret is not None, f'Expected a/an {cls.label()} but got instead: {str(pattern)}\n'
        return ret

    def __str__(self) -> str:
        return f'{self.label()} {str(self.arguments())}'

    def __eq__(self, o: object) -> bool:
        assert isinstance(o, Pattern)
        if isinstance(o, Notation) and type(o) == type(self):
            return o.arguments() == self.arguments()
        return self.conclusion() == o


@dataclass(frozen=True, eq=False)
class Bot(Notation):
    @staticmethod
    def definition() -> Pattern:
        return Mu(0, SVar(0))

    def __str__(self) -> str:
        return '\u22A5'


bot = Bot()
