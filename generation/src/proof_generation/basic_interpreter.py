from __future__ import annotations

from enum import Enum
from typing import TYPE_CHECKING

from frozendict import frozendict

from proof_generation.pattern import (
    App,
    ESubst,
    EVar,
    Exists,
    Implies,
    Instantiate,
    MetaVar,
    Mu,
    SSubst,
    SVar,
    Symbol,
    bot,
)
from proof_generation.proved import Proved

if TYPE_CHECKING:
    from collections.abc import Mapping

    from proof_generation.pattern import Pattern


class ExecutionPhase(Enum):
    Gamma = 0
    Claim = 1
    Proof = 2


class BasicInterpreter:
    """A stateless proof interpreter. It only checks conclusions."""

    def __init__(self, phase: ExecutionPhase):
        self.phase = phase
        self._interpreting_warnings: set[str] = set()

    @property
    def safe_interpreting(self) -> bool:
        return len(self._interpreting_warnings) == 0

    @property
    def interpreting_warnings(self) -> list[str]:
        return list(self._interpreting_warnings)

    def mark_generation_unsafe(self, warning: str) -> None:
        self._interpreting_warnings.add(warning)

    def into_claim_phase(self) -> None:
        assert self.phase == ExecutionPhase.Gamma
        self.phase = ExecutionPhase.Claim

    def into_proof_phase(self) -> None:
        assert self.phase == ExecutionPhase.Claim
        self.phase = ExecutionPhase.Proof

    def evar(self, id: int) -> Pattern:
        return EVar(id)

    def svar(self, id: int) -> Pattern:
        return SVar(id)

    def symbol(self, name: str) -> Pattern:
        return Symbol(name)

    def metavar(
        self,
        id: int,
        e_fresh: tuple[EVar, ...] = (),
        s_fresh: tuple[SVar, ...] = (),
        positive: tuple[SVar, ...] = (),
        negative: tuple[SVar, ...] = (),
        application_context: tuple[EVar, ...] = (),
    ) -> Pattern:
        return MetaVar(id, e_fresh, s_fresh, positive, negative, application_context)

    def implies(self, left: Pattern, right: Pattern) -> Pattern:
        return Implies(left, right)

    def app(self, left: Pattern, right: Pattern) -> Pattern:
        return App(left, right)

    def exists(self, var: int, subpattern: Pattern) -> Pattern:
        return Exists(var, subpattern)

    def esubst(self, evar_id: int, pattern: MetaVar | ESubst | SSubst, plug: Pattern) -> Pattern:
        return ESubst(pattern, EVar(evar_id), plug)

    def ssubst(self, svar_id: int, pattern: MetaVar | ESubst | SSubst, plug: Pattern) -> Pattern:
        return SSubst(pattern, SVar(svar_id), plug)

    def mu(self, var: int, subpattern: Pattern) -> Pattern:
        return Mu(var, subpattern)

    def pattern(self, p: Pattern) -> Pattern:
        match p:
            case EVar(name):
                return self.evar(name)
            case SVar(name):
                return self.svar(name)
            case Symbol(name):
                return self.symbol(name)
            case Implies(left, right):
                return self.implies(self.pattern(left), self.pattern(right))
            case App(left, right):
                return self.app(self.pattern(left), self.pattern(right))
            case Exists(var, subpattern):
                return self.exists(var, self.pattern(subpattern))
            case Mu(var, subpattern):
                return self.mu(var, self.pattern(subpattern))
            case MetaVar(name, e_fresh, s_fresh, positive, negative, app_ctx_holes):
                return self.metavar(name, e_fresh, s_fresh, positive, negative, app_ctx_holes)
            case Instantiate(subpattern, subst):
                for inst in subst.values():
                    self.pattern(inst)
                return self.instantiate_pattern(self.pattern(subpattern), subst)
            case ESubst(subpattern, var, plug):
                assert isinstance(var, EVar)
                subpattern = self.pattern(subpattern)
                assert isinstance(subpattern, MetaVar | ESubst | SSubst)
                plug = self.pattern(plug)
                return self.esubst(var.name, subpattern, plug)

        raise NotImplementedError(f'{type(p)}')

    def prop1(self) -> Proved:
        phi0: MetaVar = MetaVar(0)
        phi1: MetaVar = MetaVar(1)
        return Proved(Implies(phi0, Implies(phi1, phi0)))

    def prop2(self) -> Proved:
        phi0: MetaVar = MetaVar(0)
        phi1: MetaVar = MetaVar(1)
        phi2: MetaVar = MetaVar(2)
        return Proved(
            Implies(
                Implies(phi0, Implies(phi1, phi2)),
                Implies(Implies(phi0, phi1), Implies(phi0, phi2)),
            ),
        )

    def prop3(self) -> Proved:
        phi0: MetaVar = MetaVar(0)
        return Proved(Implies(Implies(Implies(phi0, bot()), bot()), phi0))

    def modus_ponens(self, left: Proved, right: Proved) -> Proved:
        left_conclusion = left.conclusion
        l, r = Implies.extract(left_conclusion)
        assert l == right.conclusion, str(l) + ' != ' + str(right.conclusion)
        return Proved(r)

    def exists_quantifier(self) -> Proved:
        phi = MetaVar(0)
        x = EVar(0)
        y = EVar(1)
        return Proved(Implies(ESubst(phi, x, y), Exists(x.name, phi)))

    def exists_generalization(self, proved: Proved, var: EVar) -> Proved:
        l, r = Implies.extract(proved.conclusion)
        assert r.evar_is_free(var.name), f'{str(var)} in FV({str(r)})'
        return Proved(Implies(Exists(var.name, l), r))

    def instantiate(self, proved: Proved, delta: dict[int, Pattern]) -> Proved:
        if not delta:
            return proved
        return Proved(proved.conclusion.instantiate(delta))

    def instantiate_pattern(self, pattern: Pattern, delta: Mapping[int, Pattern]) -> Pattern:
        return Instantiate(pattern, frozendict(delta))

    def pop(self, term: Pattern | Proved) -> None:
        ...

    def save(self, id: str, term: Pattern | Proved) -> None:
        ...

    def load(self, id: str, term: Pattern | Proved) -> None:
        ...

    def publish_proof(self, term: Proved) -> None:
        assert self.phase == ExecutionPhase.Proof
        ...

    def publish_axiom(self, term: Pattern) -> None:
        assert self.phase == ExecutionPhase.Gamma
        ...

    def publish_claim(self, term: Pattern) -> None:
        assert self.phase == ExecutionPhase.Claim
        ...
