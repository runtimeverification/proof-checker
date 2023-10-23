from __future__ import annotations

from dataclasses import dataclass
from typing import TYPE_CHECKING

from frozendict import frozendict

if TYPE_CHECKING:
    from collections.abc import Mapping


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
    def instantiate(self, delta: Mapping[int, Pattern]) -> Pattern:
        raise NotImplementedError

    def apply_esubst(self, evar_id: int, plug: Pattern) -> Pattern:
        raise NotImplementedError

    def apply_ssubst(self, svar_id: int, plug: Pattern) -> Pattern:
        raise NotImplementedError

    def pretty(self, opts: PrettyOptions) -> str:
        raise NotImplementedError

    def __str__(self) -> str:
        return self.pretty(PrettyOptions())

    @classmethod
    def unwrap(cls, pattern: Pattern) -> tuple[Pattern, ...] | None:
        if isinstance(pattern, Instantiate):
            return cls.unwrap(pattern.simplify())
        if isinstance(pattern, cls):
            return tuple([v for _, v in sorted(vars(pattern).items()) if isinstance(v, Pattern)])
        return None

    @classmethod
    def extract(cls, pattern: Pattern) -> tuple[Pattern, ...]:
        ret = cls.unwrap(pattern)
        assert ret is not None, f'Expected a/an {cls.__name__} but got instead: {str(pattern)}\n'
        return ret


@dataclass(frozen=True)
class EVar(Pattern):
    name: int

    def instantiate(self, delta: Mapping[int, Pattern]) -> Pattern:
        return self

    def apply_esubst(self, evar_id: int, plug: Pattern) -> Pattern:
        if evar_id == self.name:
            return plug
        return self

    def apply_ssubst(self, svar_id: int, plug: Pattern) -> Pattern:
        return self

    def pretty(self, opts: PrettyOptions) -> str:
        return f'x{self.name}'

    @staticmethod
    def deconstruct(pat: Pattern) -> int | None:
        if isinstance(pat, EVar):
            return pat.name
        if isinstance(pat, Instantiate):
            return EVar.deconstruct(pat.simplify())
        return None


@dataclass(frozen=True)
class SVar(Pattern):
    name: int

    def instantiate(self, delta: Mapping[int, Pattern]) -> Pattern:
        return self

    def apply_esubst(self, evar_id: int, plug: Pattern) -> Pattern:
        return self

    def apply_ssubst(self, svar_id: int, plug: Pattern) -> Pattern:
        if svar_id == self.name:
            return plug
        return self

    def pretty(self, opts: PrettyOptions) -> str:
        return f'X{self.name}'

    @staticmethod
    def deconstruct(pat: Pattern) -> int | None:
        if isinstance(pat, SVar):
            return pat.name
        if isinstance(pat, Instantiate):
            return SVar.deconstruct(pat.simplify())
        return None


@dataclass(frozen=True)
class Symbol(Pattern):
    name: str

    def instantiate(self, delta: Mapping[int, Pattern]) -> Pattern:
        return self

    def apply_esubst(self, evar_id: int, plug: Pattern) -> Pattern:
        return self

    def apply_ssubst(self, svar_id: int, plug: Pattern) -> Pattern:
        return self

    def pretty(self, opts: PrettyOptions) -> str:
        return f'\u03c3{self.name}'

    @staticmethod
    def deconstruct(pat: Pattern) -> str | None:
        if isinstance(pat, Symbol):
            return pat.name
        if isinstance(pat, Instantiate):
            return Symbol.deconstruct(pat.simplify())
        return None


@dataclass(frozen=True)
class Implies(Pattern):
    left: Pattern
    right: Pattern

    def instantiate(self, delta: Mapping[int, Pattern]) -> Pattern:
        return Implies(self.left.instantiate(delta), self.right.instantiate(delta))

    def apply_esubst(self, evar_id: int, plug: Pattern) -> Pattern:
        return Implies(self.left.apply_esubst(evar_id, plug), self.right.apply_esubst(evar_id, plug))

    def apply_ssubst(self, svar_id: int, plug: Pattern) -> Pattern:
        return Implies(self.left.apply_ssubst(svar_id, plug), self.right.apply_ssubst(svar_id, plug))

    def pretty(self, opts: PrettyOptions) -> str:
        return f'({self.left.pretty(opts)} -> {self.right.pretty(opts)})'


def imp(p1: Pattern, p2: Pattern) -> Pattern:
    return Implies(p1, p2)


@dataclass(frozen=True)
class App(Pattern):
    left: Pattern
    right: Pattern

    def instantiate(self, delta: Mapping[int, Pattern]) -> Pattern:
        return App(self.left.instantiate(delta), self.right.instantiate(delta))

    def apply_esubst(self, evar_id: int, plug: Pattern) -> Pattern:
        return App(self.left.apply_esubst(evar_id, plug), self.right.apply_esubst(evar_id, plug))

    def apply_ssubst(self, svar_id: int, plug: Pattern) -> Pattern:
        return App(self.left.apply_ssubst(svar_id, plug), self.right.apply_ssubst(svar_id, plug))

    def pretty(self, opts: PrettyOptions) -> str:
        return f'app({self.left.pretty(opts)}, {self.right.pretty(opts)})'


@dataclass(frozen=True)
class Exists(Pattern):
    var: int
    subpattern: Pattern

    def instantiate(self, delta: Mapping[int, Pattern]) -> Pattern:
        return Exists(self.var, self.subpattern.instantiate(delta))

    def apply_esubst(self, evar_id: int, plug: Pattern) -> Pattern:
        if evar_id == self.var:
            return self
        return Exists(self.var, self.subpattern.apply_esubst(evar_id, plug))

    def apply_ssubst(self, svar_id: int, plug: Pattern) -> Pattern:
        return Exists(self.var, self.subpattern.apply_ssubst(svar_id, plug))

    def pretty(self, opts: PrettyOptions) -> str:
        return f'(∃ x{self.var} . {self.subpattern.pretty(opts)})'

    @staticmethod
    def deconstruct(pat: Pattern) -> tuple[int, Pattern] | None:
        if isinstance(pat, Exists):
            return pat.var, pat.subpattern
        if isinstance(pat, Instantiate):
            return Exists.deconstruct(pat.simplify())
        return None


@dataclass(frozen=True)
class Mu(Pattern):
    var: int
    subpattern: Pattern

    def instantiate(self, delta: Mapping[int, Pattern]) -> Pattern:
        return Mu(self.var, self.subpattern.instantiate(delta))

    def apply_esubst(self, evar_id: int, plug: Pattern) -> Pattern:
        return Mu(self.var, self.subpattern.apply_esubst(evar_id, plug))

    def apply_ssubst(self, svar_id: int, plug: Pattern) -> Pattern:
        if svar_id == self.var:
            return self
        return Mu(self.var, self.subpattern.apply_ssubst(svar_id, plug))

    def pretty(self, opts: PrettyOptions) -> str:
        return f'(μ X{self.var} . {self.subpattern.pretty(opts)})'

    @staticmethod
    def deconstruct(pat: Pattern) -> tuple[int, Pattern] | None:
        if isinstance(pat, Mu):
            return pat.var, pat.subpattern
        if isinstance(pat, Instantiate):
            return Mu.deconstruct(pat.simplify())
        return None


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

    def instantiate(self, delta: Mapping[int, Pattern]) -> Pattern:
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

    def pretty(self, opts: PrettyOptions) -> str:
        return f'phi{self.name}'


@dataclass(frozen=True)
class ESubst(Pattern):
    pattern: MetaVar | ESubst | SSubst
    var: EVar
    plug: Pattern

    def instantiate(self, delta: Mapping[int, Pattern]) -> Pattern:
        return self.pattern.instantiate(delta).apply_esubst(self.var.name, self.plug.instantiate(delta))

    def apply_esubst(self, evar_id: int, plug: Pattern) -> Pattern:
        return ESubst(pattern=self, var=EVar(evar_id), plug=plug)

    def apply_ssubst(self, svar_id: int, plug: Pattern) -> Pattern:
        return SSubst(pattern=self, var=SVar(svar_id), plug=plug)

    def pretty(self, opts: PrettyOptions) -> str:
        return f'({self.pattern.pretty(opts)}[{self.plug.pretty(opts)}/{self.var.pretty(opts)}])'


@dataclass(frozen=True)
class SSubst(Pattern):
    pattern: MetaVar | ESubst | SSubst
    var: SVar
    plug: Pattern

    def instantiate(self, delta: Mapping[int, Pattern]) -> Pattern:
        return self.pattern.instantiate(delta).apply_ssubst(self.var.name, self.plug.instantiate(delta))

    def apply_esubst(self, evar_id: int, plug: Pattern) -> Pattern:
        return ESubst(pattern=self, var=EVar(evar_id), plug=plug)

    def apply_ssubst(self, svar_id: int, plug: Pattern) -> Pattern:
        return SSubst(pattern=self, var=SVar(svar_id), plug=plug)

    def pretty(self, opts: PrettyOptions) -> str:
        return f'({self.pattern.pretty(opts)}[{self.plug.pretty(opts)}/{self.var.pretty(opts)}])'


InstantiationDict = frozendict[int, Pattern]


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

    def instantiate(self, delta: Mapping[int, Pattern]) -> Pattern:
        instantiated_subst = frozendict({k: v.instantiate(delta) for k, v in self.inst.items()})
        unshadowed_delta = {k: v for k, v in delta.items() if k not in self.inst}
        return Instantiate(self.pattern.instantiate(unshadowed_delta), instantiated_subst)

    def apply_esubst(self, evar_id: int, plug: Pattern) -> Pattern:
        # TODO: For "complete" substitutions (where all free metavars are replaced),
        # and the substituted EVar does not occur, we should preserve the Instantiate,
        # and apply the esubst to self.inst.
        return self.simplify().apply_esubst(evar_id, plug)

    def apply_ssubst(self, svar_id: int, plug: Pattern) -> Pattern:
        # TODO: For "complete" substitutions (where all free metavars are replaced),
        # and the substituted SVar does not occur, we should preserve the Instantiate,
        # and apply the ssubst to self.inst.
        return self.simplify().apply_ssubst(svar_id, plug)

    def pretty(self, opts: PrettyOptions) -> str:
        if opts.simplify_instantiations:
            return self.simplify().pretty(opts)
        if self.pattern in opts.notations:
            return opts.notations[self.pattern].print_instantiation(self)
        return f'({str(self.pattern)}[{str(dict(self.inst))}])'


@dataclass(frozen=True)
class Notation:
    label: str
    definition: Pattern
    format_str: str

    def __call__(self, *args: Pattern) -> Pattern:
        return Instantiate(self.definition, frozendict(enumerate(args)))

    def assert_matches(self, pattern: Pattern, msg: str) -> tuple[Pattern, ...]:
        raise NotImplementedError

    def print_instantiation(self, applied: Instantiate) -> str:
        assert applied.pattern == self.definition
        return self.format_str.format(*applied.inst)


@dataclass(frozen=True)
class PrettyOptions:
    simplify_instantiations: bool = False
    notations: Mapping[Pattern, Notation] = frozendict({})


bot = Notation('bot', Mu(0, SVar(0)), '⊥')
