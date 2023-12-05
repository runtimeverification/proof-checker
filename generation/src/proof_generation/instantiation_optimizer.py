from __future__ import annotations

from typing import TYPE_CHECKING

from .basic_interpreter import BasicInterpreter
from .stateful_interpreter import StatefulInterpreter

if TYPE_CHECKING:
    from collections.abc import Mapping

    from .pattern import ESubst, EVar, MetaVar, Pattern, SSubst, SVar
    from .proved import Proved


class InterpreterTransformer(BasicInterpreter):
    """This base class allows creating an interpreter that re-interprets
    a proof in a different way.
    For example, it may optimize certain calls using the memory,
    or remove redundant patterns.
    """

    def __init__(self, output_interpreter: BasicInterpreter):
        super().__init__(output_interpreter.phase)
        self.output_interpreter = output_interpreter

    def into_claim_phase(self) -> None:
        ret = super().into_claim_phase()
        self.output_interpreter.into_claim_phase()
        return ret

    def into_proof_phase(self) -> None:
        ret = super().into_proof_phase()
        self.output_interpreter.into_proof_phase()
        return ret

    def evar(self, id: int) -> Pattern:
        ret = super().evar(id)
        self.output_interpreter.evar(id)
        return ret

    def svar(self, id: int) -> Pattern:
        ret = super().svar(id)
        self.output_interpreter.svar(id)
        return ret

    def symbol(self, name: str) -> Pattern:
        ret = super().symbol(name)
        self.output_interpreter.symbol(name)
        return ret

    def metavar(
        self,
        id: int,
        e_fresh: tuple[EVar, ...] = (),
        s_fresh: tuple[SVar, ...] = (),
        positive: tuple[SVar, ...] = (),
        negative: tuple[SVar, ...] = (),
        application_context: tuple[EVar, ...] = (),
    ) -> Pattern:
        ret = super().metavar(id, e_fresh, s_fresh, positive, negative, application_context)
        self.output_interpreter.metavar(id, e_fresh, s_fresh, positive, negative, application_context)
        return ret

    def implies(self, left: Pattern, right: Pattern) -> Pattern:
        ret = super().implies(left, right)
        self.output_interpreter.implies(left, right)
        return ret

    def app(self, left: Pattern, right: Pattern) -> Pattern:
        ret = super().app(left, right)
        self.output_interpreter.app(left, right)
        return ret

    def exists(self, var: int, subpattern: Pattern) -> Pattern:
        ret = super().exists(var, subpattern)
        self.output_interpreter.exists(var, subpattern)
        return ret

    def esubst(self, evar_id: int, pattern: MetaVar | ESubst | SSubst, plug: Pattern) -> Pattern:
        ret = super().esubst(evar_id, pattern, plug)
        self.output_interpreter.esubst(evar_id, pattern, plug)
        return ret

    def ssubst(self, svar_id: int, pattern: MetaVar | ESubst | SSubst, plug: Pattern) -> Pattern:
        ret = super().ssubst(svar_id, pattern, plug)
        self.output_interpreter.ssubst(svar_id, pattern, plug)
        return ret

    def mu(self, var: int, subpattern: Pattern) -> Pattern:
        ret = super().mu(var, subpattern)
        self.output_interpreter.mu(var, subpattern)
        return ret

    def prop1(self) -> Proved:
        ret = super().prop1()
        self.output_interpreter.prop1()
        return ret

    def prop2(self) -> Proved:
        ret = super().prop2()
        self.output_interpreter.prop2()
        return ret

    def prop3(self) -> Proved:
        ret = super().prop3()
        self.output_interpreter.prop3()
        return ret

    def modus_ponens(self, left: Proved, right: Proved) -> Proved:
        ret = super().modus_ponens(left, right)
        self.output_interpreter.modus_ponens(left, right)
        return ret

    def exists_quantifier(self) -> Proved:
        ret = super().exists_quantifier()
        self.output_interpreter.exists_quantifier()
        return ret

    def exists_generalization(self, proved: Proved, var: EVar) -> Proved:
        ret = super().exists_generalization(proved, var)
        self.output_interpreter.exists_generalization(proved, var)
        return ret

    def instantiate(self, proved: Proved, delta: dict[int, Pattern]) -> Proved:
        ret = super().instantiate(proved, delta)
        self.output_interpreter.instantiate(proved, delta)
        return ret

    def instantiate_pattern(self, pattern: Pattern, delta: Mapping[int, Pattern]) -> Pattern:
        ret = super().instantiate_pattern(pattern, delta)
        self.output_interpreter.instantiate_pattern(pattern, delta)
        return ret

    def pop(self, term: Pattern | Proved) -> None:
        ret = super().pop(term)
        self.output_interpreter.pop(term)
        return ret

    def save(self, id: str, term: Pattern | Proved) -> None:
        ret = super().save(id, term)
        self.output_interpreter.save(id, term)
        return ret

    def load(self, id: str, term: Pattern | Proved) -> None:
        ret = super().load(id, term)
        self.output_interpreter.load(id, term)
        return ret

    def publish_proof(self, term: Proved) -> None:
        ret = super().publish_proof(term)
        self.output_interpreter.publish_proof(term)
        return ret

    def publish_axiom(self, term: Pattern) -> None:
        ret = super().publish_axiom(term)
        self.output_interpreter.publish_axiom(term)
        return ret

    def publish_claim(self, term: Pattern) -> None:
        ret = super().publish_claim(term)
        self.output_interpreter.publish_claim(term)
        return ret


class InstantiationOptimizer(InterpreterTransformer):
    def __init__(self, output_interpreter: BasicInterpreter):
        super().__init__(output_interpreter)

    def instantiate(self, proved: Proved, delta: dict[int, Pattern]) -> Proved:
        untransformed = BasicInterpreter.instantiate(self, proved, delta)
        if len(delta):
            self.output_interpreter.instantiate(proved, delta)
        return untransformed

    def instantiate_pattern(self, pattern: Pattern, delta: Mapping[int, Pattern]) -> Pattern:
        untransformed = BasicInterpreter.instantiate_pattern(self, pattern, delta)
        if len(delta):
            self.output_interpreter.instantiate_pattern(pattern, delta)
        return untransformed


class MemoizingInterpreter(InterpreterTransformer):
    def __init__(self, output_interpreter: BasicInterpreter, patterns_for_memoization: set[Pattern] | None = None):
        super().__init__(output_interpreter)
        self._patterns_for_memoization: set[Pattern]
        if patterns_for_memoization is None:
            self._patterns_for_memoization = set()
        else:
            self._patterns_for_memoization = patterns_for_memoization

    def pattern(self, p: Pattern) -> Pattern:
        if isinstance(self.output_interpreter, StatefulInterpreter) and p in self.output_interpreter.memory:
            self.load(str(p), p)
            return p
        elif p in self._patterns_for_memoization:
            ret = super().pattern(p)
            self.save(repr(p), p)
            return ret
        else:
            return super().pattern(p)
