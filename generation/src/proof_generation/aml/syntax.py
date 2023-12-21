from __future__ import annotations

from abc import abstractmethod, ABC
from dataclasses import dataclass
from typing import TYPE_CHECKING

from frozendict import frozendict

if TYPE_CHECKING:
    from collections.abc import Mapping

    from .notation import Notation



class Pattern(ABC):
    def evar_is_fresh_ignoring_metavars(self, name: int, ignored_metavars: frozenset[int]) -> bool:
        raise NotImplementedError

    def evar_is_fresh(self, name: int) -> bool:
        return self.evar_is_fresh_ignoring_metavars(name, frozenset())

    def metavars(self) -> set[MetaVar]:
        raise NotImplementedError

    @abstractmethod
    def occurring_vars(self) -> set[EVar | SVar]:
        """
        Returns the set of all free variables occurring in the pattern
        Makes no guarantees about freshness!
        """

        raise NotImplementedError

    @abstractmethod
    def instantiate(self, delta: Mapping[int, Pattern]) -> Pattern:
        raise NotImplementedError

    @abstractmethod
    def apply_esubst(self, evar_id: int, plug: Pattern) -> Pattern:
        raise NotImplementedError

    @abstractmethod
    def apply_ssubst(self, svar_id: int, plug: Pattern) -> Pattern:
        raise NotImplementedError

    @abstractmethod
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

    def apply_esubsts(self, substitutions: dict[int, Pattern]) -> Pattern:
        pattern = self
        # TODO: We need apply all substitutions at once as we might want changing plugs also
        for evar_name, plug in substitutions.items():
            pattern = pattern.apply_esubst(evar_name, plug)
        return pattern


@dataclass(frozen=True)
class EVar(Pattern):
    name: int

    def evar_is_fresh_ignoring_metavars(self, name: int, ignored_metavars: frozenset[int]) -> bool:
        return name != self.name

    def metavars(self) -> set[MetaVar]:
        return set()

    def occurring_vars(self) -> set[EVar | SVar]:
        return {self}

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

    def __str__(self) -> str:
        return self.pretty(PrettyOptions())

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

    def evar_is_fresh_ignoring_metavars(self, name: int, ignored_metavars: frozenset[int]) -> bool:
        return True

    def metavars(self) -> set[MetaVar]:
        return set()

    def occurring_vars(self) -> set[EVar | SVar]:
        return {self}

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

    def __str__(self) -> str:
        return self.pretty(PrettyOptions())

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

    def evar_is_fresh_ignoring_metavars(self, name: int, ignored_metavars: frozenset[int]) -> bool:
        return True

    def metavars(self) -> set[MetaVar]:
        return set()

    def occurring_vars(self) -> set[EVar | SVar]:
        return set()

    def instantiate(self, delta: Mapping[int, Pattern]) -> Pattern:
        return self

    def apply_esubst(self, evar_id: int, plug: Pattern) -> Pattern:
        return self

    def apply_ssubst(self, svar_id: int, plug: Pattern) -> Pattern:
        return self

    def pretty(self, opts: PrettyOptions) -> str:
        return self.name

    def __str__(self) -> str:
        return self.pretty(PrettyOptions())

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

    def evar_is_fresh_ignoring_metavars(self, name: int, ignored_metavars: frozenset[int]) -> bool:
        return self.left.evar_is_fresh_ignoring_metavars(
            name, ignored_metavars
        ) and self.right.evar_is_fresh_ignoring_metavars(name, ignored_metavars)

    def metavars(self) -> set[MetaVar]:
        return self.left.metavars().union(self.right.metavars())

    def occurring_vars(self) -> set[EVar | SVar]:
        return self.left.occurring_vars().union(self.right.occurring_vars())

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

    def __str__(self) -> str:
        return self.pretty(PrettyOptions())


def imp(p1: Pattern, p2: Pattern) -> Pattern:
    return Implies(p1, p2)


@dataclass(frozen=True)
class App(Pattern):
    left: Pattern
    right: Pattern

    def evar_is_fresh_ignoring_metavars(self, name: int, ignored_metavars: frozenset[int]) -> bool:
        return self.left.evar_is_fresh_ignoring_metavars(
            name, ignored_metavars
        ) and self.right.evar_is_fresh_ignoring_metavars(name, ignored_metavars)

    def metavars(self) -> set[MetaVar]:
        return self.left.metavars().union(self.right.metavars())

    def occurring_vars(self) -> set[EVar | SVar]:
        return self.left.occurring_vars().union(self.right.occurring_vars())

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

    def __str__(self) -> str:
        return self.pretty(PrettyOptions())


@dataclass(frozen=True)
class Exists(Pattern):
    var: int
    subpattern: Pattern

    def evar_is_fresh_ignoring_metavars(self, name: int, ignored_metavars: frozenset[int]) -> bool:
        return name == self.var or self.subpattern.evar_is_fresh_ignoring_metavars(name, ignored_metavars)

    def metavars(self) -> set[MetaVar]:
        return self.subpattern.metavars()

    def occurring_vars(self) -> set[EVar | SVar]:
        return self.subpattern.occurring_vars().difference({EVar(self.var)})

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

    def __str__(self) -> str:
        return self.pretty(PrettyOptions())

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

    def __post_init__(self) -> None:
        pass
        # TODO: Add this test
        # assert self.subpattern.positive(var)

    def evar_is_fresh_ignoring_metavars(self, name: int, ignored_metavars: frozenset[int]) -> bool:
        return self.subpattern.evar_is_fresh_ignoring_metavars(name, ignored_metavars)

    def metavars(self) -> set[MetaVar]:
        return self.subpattern.metavars()

    def occurring_vars(self) -> set[EVar | SVar]:
        return self.subpattern.occurring_vars().difference({SVar(self.var)})

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

    def __str__(self) -> str:
        return self.pretty(PrettyOptions())

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

    def __post_init__(self) -> None:
        for evar_id in self.e_fresh:
            assert evar_id not in self.app_ctx_holes

    def metavars(self) -> set[MetaVar]:
        return {self}

    def evar_is_fresh_ignoring_metavars(self, name: int, ignored_metavars: frozenset[int]) -> bool:
        return self.name in ignored_metavars or EVar(name) in self.e_fresh

    def occurring_vars(self) -> set[EVar | SVar]:
        return set()

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

    def __str__(self) -> str:
        return self.pretty(PrettyOptions())


phi0 = MetaVar(0)
phi1 = MetaVar(1)
phi2 = MetaVar(2)


@dataclass(frozen=True)
class ESubst(Pattern):
    """
    Represents evar substitutions over meta-variables.
    It should almost never be used directly, instead use apply_esubst!
    """

    pattern: MetaVar | ESubst | SSubst
    var: EVar
    plug: Pattern

    def __post_init__(self) -> None:
        # Check that ESubst is not redundant
        assert self.var != self.plug
        assert not self.pattern.evar_is_fresh(self.var.name)

    def evar_is_fresh_ignoring_metavars(self, name: int, ignored_metavars: frozenset[int]) -> bool:
        if self.var.name == name:
            return self.plug.evar_is_fresh_ignoring_metavars(name, ignored_metavars)

        # This check may be slightly stronger than necessary in the case
        # where `self.var` is fresh in `self.pattern`, but `name` is not fresh in `self.plug`.
        # Since `evar_if_fresh` may return `False` when freshness in not known this is OK.
        # Indeed this option may be better for efficiency, since it is unlikely that such
        # an `ESubst` is constructed, where the user doesn't have control over its construction.
        return self.pattern.evar_is_fresh_ignoring_metavars(
            name, ignored_metavars
        ) and self.plug.evar_is_fresh_ignoring_metavars(name, ignored_metavars)

    def metavars(self) -> set[MetaVar]:
        return self.pattern.metavars().union(self.plug.metavars())

    def occurring_vars(self) -> set[EVar | SVar]:
        return self.pattern.occurring_vars().difference({self.var}).union(self.plug.occurring_vars())

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

    def __str__(self) -> str:
        return self.pretty(PrettyOptions())


@dataclass(frozen=True)
class SSubst(Pattern):
    """
    Represent svar substitutions over meta-variables.
    It should almost never be used directly, instead use apply_ssubst!
    """

    pattern: MetaVar | ESubst | SSubst
    var: SVar
    plug: Pattern

    def __post_init__(self) -> None:
        # Check that SSubst is not redundant
        assert self.var != self.plug
        # TODO: Add this check
        # assert not self.pattern.s_fresh(self.var)

    def evar_is_fresh_ignoring_metavars(self, name: int, ignored_metavars: frozenset[int]) -> bool:
        # We assume that at least one instance will be replaced
        return self.pattern.evar_is_fresh_ignoring_metavars(
            name, ignored_metavars
        ) and self.plug.evar_is_fresh_ignoring_metavars(name, ignored_metavars)

    def metavars(self) -> set[MetaVar]:
        return self.pattern.metavars().union(self.plug.metavars())

    def occurring_vars(self) -> set[EVar | SVar]:
        return self.pattern.occurring_vars().difference({self.var}).union(self.plug.occurring_vars())

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

    def __str__(self) -> str:
        return self.pretty(PrettyOptions())


InstantiationDict = frozendict[int, Pattern]


@dataclass(frozen=True)
class Instantiate(Pattern):
    """Constructor for an unsimplified Instantiated Pattern.
    This is typically used to contain Notation.
    """

    pattern: Pattern
    inst: InstantiationDict

    def simplify(self) -> Pattern:
        """
        Instantiate pattern with plug.
        Note that this doesn't fully reduce all notation, just one level.
        """
        return self.pattern.instantiate(self.inst)

    def __eq__(self, o: object) -> bool:
        # TODO: This should recursively remove all notation.
        return self.simplify() == o

    def evar_is_fresh_ignoring_metavars(self, name: int, ignored_metavars: frozenset[int]) -> bool:
        return self.pattern.evar_is_fresh_ignoring_metavars(name, ignored_metavars.union(self.inst.keys())) and all(
            value.evar_is_fresh_ignoring_metavars(name, ignored_metavars) for value in self.inst.values()
        )

    def metavars(self) -> set[MetaVar]:
        ret: set[MetaVar] = set()
        for v in self.pattern.metavars():
            if v.name in self.inst:
                ret = ret.union(self.inst[v.name].metavars())
            else:
                ret.add(v)
        return ret

    def occurring_vars(self) -> set[EVar | SVar]:
        return self.simplify().occurring_vars()

    def instantiate(self, delta: Mapping[int, Pattern]) -> Pattern:
        instantiated_subst = frozendict({k: v.instantiate(delta) for k, v in self.inst.items()})
        unshadowed_delta = {k: v for k, v in delta.items() if k not in self.inst}
        return Instantiate(self.pattern.instantiate(unshadowed_delta), instantiated_subst)

    def apply_esubst(self, evar_id: int, plug: Pattern) -> Pattern:
        if not self.pattern.evar_is_fresh_ignoring_metavars(evar_id, frozenset(self.inst.keys())):
            return self.simplify().apply_esubst(evar_id, plug)
        complete_inst = frozendict({x.name: x for x in self.pattern.metavars()}) | self.inst
        new_inst = frozendict({k: v.apply_esubst(evar_id, plug) for k, v in complete_inst.items()})
        return Instantiate(self.pattern, new_inst)

    def apply_ssubst(self, svar_id: int, plug: Pattern) -> Pattern:
        return self.simplify().apply_ssubst(svar_id, plug)

    def pretty(self, opts: PrettyOptions) -> str:
        if opts.simplify_instantiations:
            return self.simplify().pretty(opts)
        if self.pattern in opts.notations:
            n = opts.notations[self.pattern]
            if n.correctly_instantiates(self):
                return n.print_instantiation(self, opts)
        pretty_inst = []
        for key, val in sorted(self.inst.items()):
            pretty_inst += [str(key) + ': ' + val.pretty(opts)]
        return f'{str(self.pattern)}[{", ".join(pretty_inst)}]'

    def __str__(self) -> str:
        return self.pretty(PrettyOptions())


@dataclass(frozen=True)
class PrettyOptions:
    simplify_instantiations: bool = False
    notations: Mapping[Pattern, Notation] = frozendict({})
    print_stack: bool = True
