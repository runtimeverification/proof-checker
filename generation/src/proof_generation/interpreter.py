from __future__ import annotations

from abc import ABC, abstractmethod
from enum import Enum
from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from collections.abc import Mapping

    from .proved import Proved
    from .aml import Pattern

from proof_generation.aml import App, ESubst, EVar, Exists, Implies, Instantiate, MetaVar, Mu, SSubst, SVar, Symbol


class ExecutionPhase(Enum):
    Gamma = 0
    Claim = 1
    Proof = 2


class Interpreter(ABC):
    # concrete methods
    def __init__(self, phase: ExecutionPhase):
        self.phase = phase
        self._interpreting_warnings: set[str] = set()

    @property
    def safe_interpreting(self) -> bool:
        return len(self._interpreting_warnings) == 0

    @property
    def interpreting_warnings(self) -> list[str]:
        return list(self._interpreting_warnings)

    def into_claim_phase(self) -> None:
        assert self.phase == ExecutionPhase.Gamma
        self.phase = ExecutionPhase.Claim

    def into_proof_phase(self) -> None:
        assert self.phase == ExecutionPhase.Claim
        self.phase = ExecutionPhase.Proof

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
                plug = self.pattern(plug)
                subpattern = self.pattern(subpattern)
                assert isinstance(subpattern, MetaVar | ESubst | SSubst)
                return self.esubst(var.name, subpattern, plug)
            case SSubst(subpattern, var, plug):
                assert isinstance(var, SVar)
                plug = self.pattern(plug)
                subpattern = self.pattern(subpattern)
                assert isinstance(subpattern, MetaVar | ESubst | SSubst)
                return self.ssubst(var.name, subpattern, plug)

        raise NotImplementedError(f'{type(p)}')

    # abstract methods
    @abstractmethod
    def evar(self, id: int) -> Pattern:
        pass

    @abstractmethod
    def svar(self, id: int) -> Pattern:
        pass

    @abstractmethod
    def symbol(self, name: str) -> Pattern:
        pass

    @abstractmethod
    def metavar(
        self,
        id: int,
        e_fresh: tuple[EVar, ...] = (),
        s_fresh: tuple[SVar, ...] = (),
        positive: tuple[SVar, ...] = (),
        negative: tuple[SVar, ...] = (),
        application_context: tuple[EVar, ...] = (),
    ) -> Pattern:
        pass

    @abstractmethod
    def implies(self, left: Pattern, right: Pattern) -> Pattern:
        pass

    @abstractmethod
    def app(self, left: Pattern, right: Pattern) -> Pattern:
        pass

    @abstractmethod
    def exists(self, var: int, subpattern: Pattern) -> Pattern:
        pass

    @abstractmethod
    def esubst(self, evar_id: int, pattern: MetaVar | ESubst | SSubst, plug: Pattern) -> Pattern:
        pass

    @abstractmethod
    def ssubst(self, svar_id: int, pattern: MetaVar | ESubst | SSubst, plug: Pattern) -> Pattern:
        pass

    @abstractmethod
    def mu(self, var: int, subpattern: Pattern) -> Pattern:
        pass

    @abstractmethod
    def prop1(self) -> Proved:
        pass

    @abstractmethod
    def prop2(self) -> Proved:
        pass

    @abstractmethod
    def prop3(self) -> Proved:
        pass

    @abstractmethod
    def modus_ponens(self, left: Proved, right: Proved) -> Proved:
        pass

    @abstractmethod
    def exists_quantifier(self) -> Proved:
        pass

    @abstractmethod
    def exists_generalization(self, proved: Proved, var: EVar) -> Proved:
        pass

    @abstractmethod
    def instantiate(self, proved: Proved, delta: dict[int, Pattern]) -> Proved:
        pass

    @abstractmethod
    def instantiate_pattern(self, pattern: Pattern, delta: Mapping[int, Pattern]) -> Pattern:
        pass

    @abstractmethod
    def pop(self, term: Pattern | Proved) -> None:
        pass

    @abstractmethod
    def save(self, id: str, term: Pattern | Proved) -> None:
        pass

    @abstractmethod
    def load(self, id: str, term: Pattern | Proved) -> None:
        pass

    @abstractmethod
    def publish_proof(self, term: Proved) -> None:
        pass

    @abstractmethod
    def publish_axiom(self, term: Pattern) -> None:
        pass

    @abstractmethod
    def publish_claim(self, term: Pattern) -> None:
        pass
