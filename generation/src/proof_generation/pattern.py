from __future__ import annotations

from dataclasses import dataclass


def unwrap_opt(x: Pattern | None, error_msg: str) -> Pattern:
    assert x, error_msg
    return x


def unwrap_opt_2(x: tuple[Pattern, Pattern] | None, error_msg: str) -> tuple[Pattern, Pattern]:
    assert x, error_msg
    return x


class Pattern:
    def instantiate(self, delta: dict[int, Pattern]) -> Pattern:
        raise NotImplementedError

    def apply_esubst(self, evar_id: int, plug: Pattern) -> Pattern:
        raise NotImplementedError

    def apply_ssubst(self, svar_id: int, plug: Pattern) -> Pattern:
        raise NotImplementedError

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

    def __str__(self) -> str:
        return f'x{self.name}'

    def __eq__(self, o: object) -> bool:
        if isinstance(o, type(self)):
            return vars(self) == vars(o)
        else:
            return super().__eq__(o)


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

    def __eq__(self, o: object) -> bool:
        if isinstance(o, type(self)):
            return vars(self) == vars(o)
        else:
            return super().__eq__(o)


@dataclass(frozen=True)
class Symbol(Pattern):
    name: int

    def instantiate(self, delta: dict[int, Pattern]) -> Pattern:
        return self

    def apply_esubst(self, evar_id: int, plug: Pattern) -> Pattern:
        return self

    def apply_ssubst(self, svar_id: int, plug: Pattern) -> Pattern:
        return self

    def __str__(self) -> str:
        return f'\u03c3{str(self.name)}'

    def __eq__(self, o: object) -> bool:
        if isinstance(o, type(self)):
            return vars(self) == vars(o)
        else:
            return super().__eq__(o)


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

    @staticmethod
    def unwrap(pat: Pattern) -> tuple[Pattern, Pattern] | None:
        if isinstance(pat, Implication):
            return pat.left, pat.right
        if isinstance(pat, Notation):
            return Implication.unwrap(pat.conclusion())
        return None

    @staticmethod
    def extract(pat: Pattern) -> tuple[Pattern, Pattern]:
        return unwrap_opt_2(Implication.unwrap(pat), 'Expected an implication but got: ' + str(pat) + '\n')

    def __eq__(self, o: object) -> bool:
        if isinstance(o, type(self)):
            return vars(self) == vars(o)
        else:
            return super().__eq__(o)


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

    def __str__(self) -> str:
        return f'(app ({str(self.left)}) ({str(self.right)}))'

    def __eq__(self, o: object) -> bool:
        if isinstance(o, type(self)):
            return vars(self) == vars(o)
        else:
            return super().__eq__(o)


@dataclass(frozen=True)
class Exists(Pattern):
    var: EVar
    subpattern: Pattern

    def instantiate(self, delta: dict[int, Pattern]) -> Pattern:
        return Exists(self.var, self.subpattern.instantiate(delta))

    def apply_esubst(self, evar_id: int, plug: Pattern) -> Pattern:
        if EVar(evar_id) == self.var:
            return self
        return Exists(self.var, self.subpattern.apply_esubst(evar_id, plug))

    def apply_ssubst(self, svar_id: int, plug: Pattern) -> Pattern:
        return Exists(self.var, self.subpattern.apply_ssubst(svar_id, plug))

    def __str__(self) -> str:
        return f'(\u2203 {str(self.var)} . {str(self.subpattern)})'

    def __eq__(self, o: object) -> bool:
        if isinstance(o, type(self)):
            return vars(self) == vars(o)
        else:
            return super().__eq__(o)


@dataclass(frozen=True)
class Mu(Pattern):
    var: SVar
    subpattern: Pattern

    def instantiate(self, delta: dict[int, Pattern]) -> Pattern:
        return Mu(self.var, self.subpattern.instantiate(delta))

    def apply_esubst(self, evar_id: int, plug: Pattern) -> Pattern:
        return Mu(self.var, self.subpattern.apply_esubst(evar_id, plug))

    def apply_ssubst(self, svar_id: int, plug: Pattern) -> Pattern:
        if SVar(svar_id) == self.var:
            return self
        return Mu(self.var, self.subpattern.apply_ssubst(svar_id, plug))

    def __str__(self) -> str:
        return f'(\u03BC {str(self.var)} . {str(self.subpattern)})'

    def __eq__(self, o: object) -> bool:
        if isinstance(o, type(self)):
            return vars(self) == vars(o)
        else:
            return super().__eq__(o)


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

    def __eq__(self, o: object) -> bool:
        if isinstance(o, type(self)):
            return vars(self) == vars(o)
        else:
            return super().__eq__(o)


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

    def __eq__(self, o: object) -> bool:
        if isinstance(o, type(self)):
            return vars(self) == vars(o)
        else:
            return super().__eq__(o)


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

    def __eq__(self, o: object) -> bool:
        if isinstance(o, type(self)):
            return vars(self) == vars(o)
        else:
            return super().__eq__(o)


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

    def __eq__(self, o: object) -> bool:
        assert isinstance(o, Pattern)
        if isinstance(o, Notation) and type(o) == type(self):
            return o.arguments() == self.arguments()
        return self.conclusion() == o

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

    def __str__(self) -> str:
        return f'{self.label()} {str(self.arguments())}'


@dataclass(frozen=True, eq=False)
class Bot(Notation):
    @staticmethod
    def definition() -> Pattern:
        return Mu(SVar(0), SVar(0))

    def __str__(self) -> str:
        return '\u22A5'

    @staticmethod
    def is_bot(pat: Pattern) -> bool:
        if isinstance(pat, Bot):
            return True
        if isinstance(pat, Notation):
            return Bot.is_bot(pat.conclusion())
        if pat == bot.conclusion():
            return True
        return False

    @staticmethod
    def extract(pat: Pattern) -> None:
        assert Bot.is_bot(pat), 'Expected Bot but instead got: ' + str(pat) + '\n'


bot = Bot()
