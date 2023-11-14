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
        return ret
    if (pat_imp := Implies.unwrap(pattern)) and (inst_imp := Implies.unwrap(instance)):
        ret = match_single(pat_imp[0], inst_imp[0], ret)
        if ret is None:
            return None
        return match_single(pat_imp[1], inst_imp[1], ret)
    # The following three cases are more verbose because a 0 returned by the
    # deconstruct is still interpreted as False even though it is not None
    pat_evar = EVar.deconstruct(pattern)
    inst_evar = EVar.deconstruct(instance)
    if (pat_evar is not None) and (inst_evar is not None):
        if pat_evar != inst_evar:
            return None
        return ret
    pat_svar = SVar.deconstruct(pattern)
    inst_svar = SVar.deconstruct(instance)
    if (pat_svar is not None) and (inst_svar is not None):
        if pat_svar != inst_svar:
            return None
        return ret
    pat_sym = Symbol.deconstruct(pattern)
    inst_sym = Symbol.deconstruct(instance)
    if (pat_sym is not None) and (inst_sym is not None):
        if pat_sym != inst_sym:
            return None
        return ret
    if (pat_app := App.unwrap(pattern)) and (inst_app := App.unwrap(instance)):
        ret = match_single(pat_app[0], inst_app[0], ret)
        if ret is None:
            return None
        return match_single(pat_app[1], inst_app[1], ret)
    if (pat_ex := Exists.deconstruct(pattern)) and (inst_ex := Exists.deconstruct(instance)):
        if pat_ex[0] != inst_ex[0]:
            return None
        return match_single(pat_ex[1], inst_ex[1], ret)
    if (pat_mu := Mu.deconstruct(pattern)) and (inst_mu := Mu.deconstruct(instance)):
        if pat_mu[0] != inst_mu[0]:
            return None
        return match_single(pat_mu[1], inst_mu[1], ret)
    # TODO Consider adding cases for ESubst/SSubst
    return None


def match(equations: list[tuple[Pattern, Pattern]]) -> dict[int, Pattern] | None:
    ret: dict[int, Pattern] = {}
    for pattern, instance in equations:
        submatch = match_single(pattern, instance, ret)
        if not submatch:
            return None
        ret = submatch
    return ret


class Pattern:
    def evar_is_free(self, name: int) -> bool:
        raise NotImplementedError

    def metavars(self) -> set[int]:
        raise NotImplementedError

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

    def evar_is_free(self, name: int) -> bool:
        return name != self.name

    def metavars(self) -> set[int]:
        return set()

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

    def evar_is_free(self, name: int) -> bool:
        return True

    def metavars(self) -> set[int]:
        return set()

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

    def evar_is_free(self, name: int) -> bool:
        return True

    def metavars(self) -> set[int]:
        return set()

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

    def evar_is_free(self, name: int) -> bool:
        return self.left.evar_is_free(name) and self.right.evar_is_free(name)

    def metavars(self) -> set[int]:
        return self.left.metavars().union(self.right.metavars())

    def instantiate(self, delta: Mapping[int, Pattern]) -> Pattern:
        if not delta:
            return self
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

    def evar_is_free(self, name: int) -> bool:
        return self.left.evar_is_free(name) and self.right.evar_is_free(name)

    def metavars(self) -> set[int]:
        return self.left.metavars().union(self.right.metavars())

    def instantiate(self, delta: Mapping[int, Pattern]) -> Pattern:
        if not delta:
            return self
        return App(self.left.instantiate(delta), self.right.instantiate(delta))

    def apply_esubst(self, evar_id: int, plug: Pattern) -> Pattern:
        return App(self.left.apply_esubst(evar_id, plug), self.right.apply_esubst(evar_id, plug))

    def apply_ssubst(self, svar_id: int, plug: Pattern) -> Pattern:
        return App(self.left.apply_ssubst(svar_id, plug), self.right.apply_ssubst(svar_id, plug))

    def pretty(self, opts: PrettyOptions) -> str:
        return f'({self.left.pretty(opts)} · {self.right.pretty(opts)})'


@dataclass(frozen=True)
class Exists(Pattern):
    var: int
    subpattern: Pattern

    def evar_is_free(self, name: int) -> bool:
        return name == self.var or self.subpattern.evar_is_free(name)

    def metavars(self) -> set[int]:
        return self.subpattern.metavars()

    def instantiate(self, delta: Mapping[int, Pattern]) -> Pattern:
        if not delta:
            return self
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

    def evar_is_free(self, name: int) -> bool:
        return self.subpattern.evar_is_free(name)

    def metavars(self) -> set[int]:
        return self.subpattern.metavars()

    def instantiate(self, delta: Mapping[int, Pattern]) -> Pattern:
        if not delta:
            return self
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

    def metavars(self) -> set[int]:
        return {self.name}

    def evar_is_free(self, name: int) -> bool:
        return EVar(name) in self.e_fresh

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


phi0 = MetaVar(0)
phi1 = MetaVar(1)
phi2 = MetaVar(2)


@dataclass(frozen=True)
class ESubst(Pattern):
    pattern: MetaVar | ESubst | SSubst
    var: EVar
    plug: Pattern

    def evar_is_free(self, name: int) -> bool:
        if self.var.name == name:
            return self.plug.evar_is_free(name)

        # We assume that at least one instance will be replaced
        return self.pattern.evar_is_free(name) and self.plug.evar_is_free(name)

    def metavars(self) -> set[int]:
        return self.pattern.metavars().union(self.plug.metavars())

    def instantiate(self, delta: Mapping[int, Pattern]) -> Pattern:
        if not delta:
            return self
        return self.pattern.instantiate(delta).apply_esubst(self.var.name, self.plug.instantiate(delta))

    def apply_esubst(self, evar_id: int, plug: Pattern) -> Pattern:
        return ESubst(pattern=self, var=EVar(evar_id), plug=plug)

    def apply_ssubst(self, svar_id: int, plug: Pattern) -> Pattern:
        return SSubst(pattern=self, var=SVar(svar_id), plug=plug)

    def pretty(self, opts: PrettyOptions) -> str:
        return f'{self.pattern.pretty(opts)}[{self.plug.pretty(opts)}/{self.var.pretty(opts)}]'


@dataclass(frozen=True)
class SSubst(Pattern):
    pattern: MetaVar | ESubst | SSubst
    var: SVar
    plug: Pattern

    def evar_is_free(self, name: int) -> bool:
        # We assume that at least one instance will be replaced
        return self.pattern.evar_is_free(name) and self.plug.evar_is_free(name)

    def metavars(self) -> set[int]:
        return self.pattern.metavars().union(self.plug.metavars())

    def instantiate(self, delta: Mapping[int, Pattern]) -> Pattern:
        if not delta:
            return self
        return self.pattern.instantiate(delta).apply_ssubst(self.var.name, self.plug.instantiate(delta))

    def apply_esubst(self, evar_id: int, plug: Pattern) -> Pattern:
        return ESubst(pattern=self, var=EVar(evar_id), plug=plug)

    def apply_ssubst(self, svar_id: int, plug: Pattern) -> Pattern:
        return SSubst(pattern=self, var=SVar(svar_id), plug=plug)

    def pretty(self, opts: PrettyOptions) -> str:
        return f'{self.pattern.pretty(opts)}[{self.plug.pretty(opts)}/{self.var.pretty(opts)}]'


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

    def evar_is_free(self, name: int) -> bool:
        return self.pattern.evar_is_free(name) or any(value.evar_is_free(name) for value in self.inst.values())

    def metavars(self) -> set[int]:
        ret: set[int] = set()
        for v in self.pattern.metavars():
            if v in self.inst:
                ret = ret.union(self.inst[v].metavars())
            else:
                ret.add(v)
        return ret

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
            return opts.notations[self.pattern].print_instantiation(self, opts)
        pretty_inst = {}
        for (key, val) in self.inst.items():
            pretty_inst[key] = val.pretty(opts)
        return f'{str(self.pattern)}[{str(pretty_inst)}]'


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
        return self.format_str.format(*(p.pretty(opts) for p in applied.inst.values()))


@dataclass(frozen=True)
class PrettyOptions:
    simplify_instantiations: bool = False
    notations: Mapping[Pattern, Notation] = frozendict({})


bot = Notation('bot', 0, Mu(0, SVar(0)), '⊥')
