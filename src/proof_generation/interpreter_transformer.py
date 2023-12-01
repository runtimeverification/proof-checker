from __future__ import annotations

from typing import TYPE_CHECKING

from proof_generation.interpreter import Interpreter

if TYPE_CHECKING:
    from collections.abc import Mapping

    from .pattern import ESubst, EVar, MetaVar, Pattern, SSubst, SVar
    from .proved import Proved


class InterpreterTransformer(Interpreter):
    """This base class allows creating a transformer interpreter that
    re-interprets a proof in a different way.
    For example, it may optimize certain calls using the memory,
    or remove redundant patterns.
    Note that transformers can, in general, be arbitrarily nested.
    sub_interpreter refers to the wrapped interpreter, while
    core_interpreter refers to the innermost (non-transformer)
    interpreter (which doesn't wrap an interpreter).
    """

    def __init__(self, sub_interpreter: Interpreter):
        super().__init__(sub_interpreter.phase)
        self.sub_interpreter = sub_interpreter
        self.core_interpreter: Interpreter
        if isinstance(sub_interpreter, InterpreterTransformer):
            self.core_interpreter = sub_interpreter.core_interpreter
        else:
            self.core_interpreter = sub_interpreter

    def into_claim_phase(self) -> None:
        super().into_claim_phase()
        self.sub_interpreter.into_claim_phase()

    def into_proof_phase(self) -> None:
        super().into_proof_phase()
        self.sub_interpreter.into_proof_phase()

    def evar(self, id: int) -> Pattern:
        ret = self.sub_interpreter.evar(id)
        return ret

    def svar(self, id: int) -> Pattern:
        ret = self.sub_interpreter.svar(id)
        return ret

    def symbol(self, name: str) -> Pattern:
        ret = self.sub_interpreter.symbol(name)
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
        ret = self.sub_interpreter.metavar(id, e_fresh, s_fresh, positive, negative, application_context)
        return ret

    def implies(self, left: Pattern, right: Pattern) -> Pattern:
        ret = self.sub_interpreter.implies(left, right)
        return ret

    def app(self, left: Pattern, right: Pattern) -> Pattern:
        ret = self.sub_interpreter.app(left, right)
        return ret

    def exists(self, var: int, subpattern: Pattern) -> Pattern:
        ret = self.sub_interpreter.exists(var, subpattern)
        return ret

    def esubst(self, evar_id: int, pattern: MetaVar | ESubst | SSubst, plug: Pattern) -> Pattern:
        ret = self.sub_interpreter.esubst(evar_id, pattern, plug)
        return ret

    def ssubst(self, svar_id: int, pattern: MetaVar | ESubst | SSubst, plug: Pattern) -> Pattern:
        ret = self.sub_interpreter.ssubst(svar_id, pattern, plug)
        return ret

    def mu(self, var: int, subpattern: Pattern) -> Pattern:
        ret = self.sub_interpreter.mu(var, subpattern)
        return ret

    def prop1(self) -> Proved:
        ret = self.sub_interpreter.prop1()
        return ret

    def prop2(self) -> Proved:
        ret = self.sub_interpreter.prop2()
        return ret

    def prop3(self) -> Proved:
        ret = self.sub_interpreter.prop3()
        return ret

    def modus_ponens(self, left: Proved, right: Proved) -> Proved:
        ret = self.sub_interpreter.modus_ponens(left, right)
        return ret

    def exists_quantifier(self) -> Proved:
        ret = self.sub_interpreter.exists_quantifier()
        return ret

    def exists_generalization(self, proved: Proved, var: EVar) -> Proved:
        ret = self.sub_interpreter.exists_generalization(proved, var)
        return ret

    def instantiate(self, proved: Proved, delta: dict[int, Pattern]) -> Proved:
        ret = self.sub_interpreter.instantiate(proved, delta)
        return ret

    def instantiate_pattern(self, pattern: Pattern, delta: Mapping[int, Pattern]) -> Pattern:
        ret = self.sub_interpreter.instantiate_pattern(pattern, delta)
        return ret

    def pop(self, term: Pattern | Proved) -> None:
        self.sub_interpreter.pop(term)

    def save(self, id: str, term: Pattern | Proved) -> None:
        self.sub_interpreter.save(id, term)

    def load(self, id: str, term: Pattern | Proved) -> None:
        self.sub_interpreter.load(id, term)

    def publish_proof(self, term: Proved) -> None:
        self.sub_interpreter.publish_proof(term)

    def publish_axiom(self, term: Pattern) -> None:
        self.sub_interpreter.publish_axiom(term)

    def publish_claim(self, term: Pattern) -> None:
        self.sub_interpreter.publish_claim(term)
