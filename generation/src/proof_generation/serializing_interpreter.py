from __future__ import annotations

from typing import TYPE_CHECKING, Any, BinaryIO

from proof_generation.instruction import Instruction
from proof_generation.io_interpreter import IOInterpreter

if TYPE_CHECKING:
    from proof_generation.basic_interpreter import ExecutionPhase
    from proof_generation.claim import Claim
    from proof_generation.io_interpreter import IO
    from proof_generation.pattern import ESubst, EVar, MetaVar, Pattern, SSubst, SVar
    from proof_generation.proved import Proved


class SerializingInterpreter(IOInterpreter):
    def __init__(
        self,
        phase: ExecutionPhase,
        out: IO[Any],
        claims: list[Claim] | None = None,
        claim_out: IO[Any] | None = None,
        proof_out: IO[Any] | None = None,
    ) -> None:
        super().__init__(phase, out, claims, claim_out, proof_out)
        self._symbol_identifiers: dict[str, int] = {}

    def evar(self, id: int) -> Pattern:
        ret = super().evar(id)
        self.out.write(bytes([Instruction.EVar, id]))
        return ret

    def svar(self, id: int) -> Pattern:
        ret = super().svar(id)
        self.out.write(bytes([Instruction.SVar, id]))
        return ret

    def symbol(self, name: str) -> Pattern:
        ret = super().symbol(name)

        if name not in self._symbol_identifiers:
            self._symbol_identifiers[name] = len(self._symbol_identifiers)
        id = self._symbol_identifiers[name]
        self.out.write(bytes([Instruction.Symbol, id]))
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
        lists: list[tuple[EVar, ...] | tuple[SVar, ...]] = [e_fresh, s_fresh, positive, negative, application_context]

        if sum([len(list) for list in lists]) == 0:
            # If all arrays are empty, metavar is "clean", we use a more succint instruction
            self.out.write(bytes([Instruction.CleanMetaVar, id]))
        else:
            self.out.write(bytes([Instruction.MetaVar, id]))
            for list in lists:
                self.out.write(bytes([len(list), *[var.name for var in list]]))
        return ret

    def implies(self, left: Pattern, right: Pattern) -> Pattern:
        ret = super().implies(left, right)
        self.out.write(bytes([Instruction.Implies]))
        return ret

    def app(self, left: Pattern, right: Pattern) -> Pattern:
        ret = super().app(left, right)
        self.out.write(bytes([Instruction.App]))
        return ret

    def exists(self, var: int, subpattern: Pattern) -> Pattern:
        ret = super().exists(var, subpattern)
        self.out.write(bytes([Instruction.Exists, var]))
        return ret

    def mu(self, var: int, subpattern: Pattern) -> Pattern:
        ret = super().mu(var, subpattern)
        self.out.write(bytes([Instruction.Mu, var]))
        return ret

    def esubst(self, evar_id: int, pattern: MetaVar | ESubst | SSubst, plug: Pattern) -> Pattern:
        ret = super().esubst(evar_id, pattern, plug)
        self.out.write(bytes([Instruction.ESubst, evar_id]))
        return ret

    def ssubst(self, svar_id: int, pattern: MetaVar | ESubst | SSubst, plug: Pattern) -> Pattern:
        ret = super().ssubst(svar_id, pattern, plug)
        self.out.write(bytes([Instruction.SSubst, svar_id]))
        return ret

    def prop1(self) -> Proved:
        ret = super().prop1()
        self.out.write(bytes([Instruction.Prop1]))
        return ret

    def prop2(self) -> Proved:
        ret = super().prop2()
        self.out.write(bytes([Instruction.Prop2]))
        return ret

    def prop3(self) -> Proved:
        ret = super().prop3()
        self.out.write(bytes([Instruction.Prop3]))
        return ret

    def modus_ponens(self, left: Proved, right: Proved) -> Proved:
        ret = super().modus_ponens(left, right)
        self.out.write(bytes([Instruction.ModusPonens]))
        return ret

    def exists_quantifier(self) -> Proved:
        ret = super().exists_quantifier()
        self.out.write(bytes([Instruction.Quantifier]))
        return ret

    def exists_generalization(self, proved: Proved, var: EVar) -> Proved:
        ret = super().exists_generalization(proved, var)
        self.out.write(bytes([Instruction.Generalization, var.name]))
        return ret

    def instantiate(self, proved: Proved, delta: dict[int, Pattern]) -> Proved:
        ret = super().instantiate(proved, delta)
        self.out.write(bytes([Instruction.Instantiate, len(delta), *reversed(delta.keys())]))
        return ret

    def instantiate_pattern(self, pattern: Pattern, delta: dict[int, Pattern]) -> Pattern:
        ret = super().instantiate_pattern(pattern, delta)
        self.out.write(bytes([Instruction.Instantiate, len(delta), *reversed(delta.keys())]))
        return ret

    def pop(self, term: Pattern | Proved) -> None:
        super().pop(term)
        self.out.write(bytes([Instruction.Pop]))

    def save(self, id: str, term: Pattern | Proved) -> None:
        ret = super().save(id, term)
        self.out.write(bytes([Instruction.Save]))
        return ret

    def load(self, id: str, term: Pattern | Proved) -> None:
        ret = super().load(id, term)
        self.out.write(bytes([Instruction.Load, self.memory.index(term)]))
        return ret

    def publish_proof(self, proved: Proved) -> None:
        super().publish_proof(proved)
        self.out.write(bytes([Instruction.Publish]))

    def publish_axiom(self, axiom: Pattern) -> None:
        super().publish_axiom(axiom)
        self.out.write(bytes([Instruction.Publish]))

    def publish_claim(self, pattern: Pattern) -> None:
        super().publish_claim(pattern)
        self.out.write(bytes([Instruction.Publish]))


class MemoizingInterpreter(SerializingInterpreter):
    def __init__(
        self,
        phase: ExecutionPhase,
        out: BinaryIO,
        claims: list[Claim] | None = None,
        patterns_for_memoization: set[Pattern] | None = None,
        claim_out: BinaryIO | None = None,
        proof_out: BinaryIO | None = None,
    ) -> None:
        super().__init__(phase, out, claims, claim_out, proof_out)
        self._patterns_for_memoization: set[Pattern]
        if patterns_for_memoization is None:
            self._patterns_for_memoization = set()
        else:
            self._patterns_for_memoization = patterns_for_memoization

    def pattern(self, p: Pattern) -> Pattern:
        if p in self.memory:
            self.load(str(p), p)
            return p
        elif p in self._patterns_for_memoization:
            ret = super().pattern(p)
            self.save(repr(p), p)
            return ret
        else:
            return super().pattern(p)
