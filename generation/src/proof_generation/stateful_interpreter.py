from __future__ import annotations

from typing import TYPE_CHECKING

from proof_generation.basic_interpreter import BasicInterpreter
from proof_generation.proved import Proved

if TYPE_CHECKING:
    from collections.abc import Mapping

    from proof_generation.aml import ESubst, EVar, MetaVar, Pattern, SSubst, SVar
    from proof_generation.claim import Claim
    from proof_generation.interpreter import ExecutionPhase


class StatefulInterpreter(BasicInterpreter):
    """A Proof interpreter that also keeps track of the verifier state,
    such as the memory, stack and claims remaining.
    """

    claims: list[Claim]
    stack: list[Pattern | Proved]
    memory: list[Pattern | Proved]

    def __init__(
        self,
        phase: ExecutionPhase,
        claims: list[Claim] | None = None,
    ) -> None:
        super().__init__(phase=phase)
        self.stack = []
        self.memory = []
        self.claims = claims if claims else []

    def into_claim_phase(self) -> None:
        self.stack = []
        super().into_claim_phase()

    def into_proof_phase(self) -> None:
        self.stack = []
        super().into_proof_phase()

    def print_state(self) -> None:
        for i, item in enumerate(self.stack):
            print(i, item)

    def evar(self, id: int) -> Pattern:
        ret = super().evar(id)
        self.stack.append(ret)
        return ret

    def svar(self, id: int) -> Pattern:
        ret = super().svar(id)
        self.stack.append(ret)
        return ret

    def symbol(self, name: str) -> Pattern:
        ret = super().symbol(name)
        self.stack.append(ret)
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
        self.stack.append(ret)
        return ret

    def implies(self, left: Pattern, right: Pattern) -> Pattern:
        *self.stack, expected_left, expected_right = self.stack
        assert expected_left == left
        assert expected_right == right
        ret = super().implies(left, right)
        self.stack.append(ret)
        return ret

    def app(self, left: Pattern, right: Pattern) -> Pattern:
        *self.stack, expected_left, expected_right = self.stack
        assert expected_left == left
        assert expected_right == right
        ret = super().app(left, right)
        self.stack.append(ret)
        return ret

    def exists(self, var: int, subpattern: Pattern) -> Pattern:
        *self.stack, expected_subpattern = self.stack
        assert expected_subpattern == subpattern
        ret = super().exists(var, subpattern)
        self.stack.append(ret)
        return ret

    def mu(self, var: int, subpattern: Pattern) -> Pattern:
        *self.stack, expected_subpattern = self.stack
        assert expected_subpattern == subpattern
        ret = super().mu(var, subpattern)
        self.stack.append(ret)
        return ret

    def esubst(self, evar_id: int, pattern: MetaVar | ESubst | SSubst, plug: Pattern) -> Pattern:
        *self.stack, expected_plug, expected_pattern = self.stack
        assert expected_pattern == pattern
        assert expected_plug == plug
        ret = super().esubst(evar_id, pattern, plug)
        self.stack.append(ret)
        return ret

    def ssubst(self, svar_id: int, pattern: MetaVar | ESubst | SSubst, plug: Pattern) -> Pattern:
        *self.stack, expected_plug, expected_pattern = self.stack
        assert expected_pattern == pattern
        assert expected_plug == plug
        ret = super().ssubst(svar_id, pattern, plug)
        self.stack.append(ret)
        return ret

    def prop1(self) -> Proved:
        ret = super().prop1()
        self.stack.append(ret)
        return ret

    def prop2(self) -> Proved:
        ret = super().prop2()
        self.stack.append(ret)
        return ret

    def prop3(self) -> Proved:
        ret = super().prop3()
        self.stack.append(ret)
        return ret

    def modus_ponens(self, left: Proved, right: Proved) -> Proved:
        *self.stack, expected_left, expected_right = self.stack
        assert expected_left == left, f'expected: {expected_left}\ngot: {left}'
        assert expected_right == right, f'expected: {expected_right}\ngot: {right}'
        ret = super().modus_ponens(left, right)
        self.stack.append(ret)
        return ret

    def exists_quantifier(self) -> Proved:
        ret = super().exists_quantifier()
        self.stack.append(ret)
        return ret

    def exists_generalization(self, proved: Proved, var: EVar) -> Proved:
        *self.stack, expected = self.stack
        assert expected == proved, f'expected: {expected}\ngot: {proved}'
        ret = super().exists_generalization(proved, var)
        self.stack.append(ret)
        return ret

    def instantiate(self, proved: Proved, delta: dict[int, Pattern]) -> Proved:
        *self.stack, expected_proved = self.stack
        expected_plugs = self.stack[-len(delta) :]
        self.stack = self.stack[: -len(delta)]

        assert expected_proved == proved, f'expected: {expected_proved}\ngot: {proved}'
        assert expected_plugs == list(delta.values()), f'expected: {expected_plugs}\ngot: {list(delta.values())}'
        ret = super().instantiate(proved, delta)
        self.stack.append(ret)
        return ret

    def instantiate_pattern(self, pattern: Pattern, delta: Mapping[int, Pattern]) -> Pattern:
        *self.stack, expected_pattern = self.stack
        expected_plugs = []
        if len(delta):
            expected_plugs = self.stack[-len(delta) :]
            self.stack = self.stack[: -len(delta)]

        assert expected_pattern == pattern, f'expected: {expected_pattern}\ngot: {pattern}'
        assert expected_plugs == list(delta.values()), f'expected: {expected_plugs}\ngot: {list(delta.values())}'
        ret = super().instantiate_pattern(pattern, delta)
        self.stack.append(ret)
        return ret

    def pop(self, term: Pattern | Proved) -> None:
        assert self.stack[-1] == term, f'expected: {self.stack[-1]}\ngot: {term}'
        self.stack.pop()
        super().pop(term)

    def save(self, id: str, term: Pattern | Proved) -> None:
        assert self.stack[-1] == term, f'expected: {self.stack[-1]}\ngot: {term}'
        self.memory.append(term)
        super().save(id, term)

    def load(self, id: str, term: Pattern | Proved) -> None:
        assert term in self.memory
        self.stack.append(term)
        super().load(id, term)

    def publish_proof(self, proved: Proved) -> None:
        super().publish_proof(proved)
        expected_claim, *self.claims = self.claims
        assert (
            proved.conclusion == expected_claim.pattern
        ), f'{str(proved.conclusion)} != {str(expected_claim.pattern)} \n {str(self.stack)}'
        assert self.stack[-1] == proved, f'{str(self.stack[-1])} != {str(proved)} \n {str(self.stack)}'

    def publish_axiom(self, axiom: Pattern) -> None:
        self.memory.append(Proved(axiom))
        super().publish_axiom(axiom)
        assert self.stack[-1] == axiom

    def publish_claim(self, pattern: Pattern) -> None:
        super().publish_claim(pattern)
        assert self.stack[-1] == pattern
