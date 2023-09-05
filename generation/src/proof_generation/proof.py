from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass
from enum import Enum
from functools import partial
from pathlib import Path
from typing import BinaryIO, TextIO

from proof_generation.instruction import Instruction
from proof_generation.pattern import (
    Application,
    ESubst,
    EVar,
    Exists,
    Implication,
    MetaVar,
    Mu,
    Pattern,
    SSubst,
    SVar,
    Symbol,
)


class ExecutionPhase(Enum):
    Gamma = 0
    Claim = 1
    Proof = 2


@dataclass
class Proved:
    interpreter: BasicInterpreter
    conclusion: Pattern

    def instantiate(self: Proved, delta: dict[int, Pattern]) -> Proved:
        for idn, p in delta.items():
            delta[idn] = self.interpreter.pattern(p)

        return self.interpreter.instantiate(self, delta)

    def assertc(self, pattern: Pattern) -> Proved:
        assert self.conclusion == pattern
        return self

    def __str__(self) -> str:
        return str(self.conclusion)


# Proof Expressions
# =================


class BasicInterpreter:
    """A stateless proof interpreter. It only checks conclusions."""

    def __init__(self, phase: ExecutionPhase):
        self.phase = phase

    def evar(self, id: int) -> Pattern:
        return EVar(id)

    def svar(self, id: int) -> Pattern:
        return SVar(id)

    def symbol(self, id: int) -> Pattern:
        return Symbol(id)

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
        return Implication(left, right)

    def app(self, left: Pattern, right: Pattern) -> Pattern:
        return Application(left, right)

    def exists(self, var: int, subpattern: Pattern) -> Pattern:
        return Exists(EVar(var), subpattern)

    def mu(self, var: int, subpattern: Pattern) -> Pattern:
        return Mu(SVar(var), subpattern)

    def pattern(self, p: Pattern) -> Pattern:
        match p:
            case EVar(name):
                return self.evar(name)
            case SVar(name):
                return self.svar(name)
            case Symbol(name):
                return self.symbol(name)
            case Implication(left, right):
                return self.implies(self.pattern(left), self.pattern(right))
            case Application(left, right):
                return self.app(self.pattern(left), self.pattern(right))
            case Exists(var, subpattern):
                return self.exists(var.name, self.pattern(subpattern))
            case Mu(var, subpattern):
                return self.mu(var.name, self.pattern(subpattern))
            case MetaVar(name, e_fresh, s_fresh, positive, negative, app_ctx_holes):
                # TODO: The results should be passed to self.metavar
                self.patterns(e_fresh)
                self.patterns(s_fresh)
                self.patterns(positive)
                self.patterns(negative)
                self.patterns(app_ctx_holes)

                return self.metavar(name, e_fresh, s_fresh, positive, negative, app_ctx_holes)

        raise NotImplementedError

    def patterns(self, ps: tuple[Pattern, ...]) -> tuple[Pattern, ...]:
        return tuple(self.pattern(p) for p in ps)

    def prop1(self) -> Proved:
        phi0: MetaVar = MetaVar(0)
        phi1: MetaVar = MetaVar(1)
        return Proved(self, Implication(phi0, Implication(phi1, phi0)))

    def prop2(self) -> Proved:
        phi0: MetaVar = MetaVar(0)
        phi1: MetaVar = MetaVar(1)
        phi2: MetaVar = MetaVar(2)
        return Proved(
            self,
            Implication(
                Implication(phi0, Implication(phi1, phi2)),
                Implication(Implication(phi0, phi1), Implication(phi0, phi2)),
            ),
        )

    def prop3(self) -> Proved:
        phi0: MetaVar = MetaVar(0)
        bot: Pattern = Mu(SVar(0), SVar(0))
        return Proved(self, Implication(Implication(Implication(phi0, bot), bot), phi0))

    def modus_ponens(self, left: Proved, right: Proved) -> Proved:
        left_conclusion = left.conclusion
        assert isinstance(left_conclusion, Implication)
        assert left_conclusion.left == right.conclusion, (left_conclusion.left, right.conclusion)
        return Proved(self, left_conclusion.right)

    def instantiate(self, proved: Proved, delta: dict[int, Pattern]) -> Proved:
        return Proved(self, proved.conclusion.instantiate(delta))

    def instantiate_notation(self, pattern: Pattern, delta: dict[int, Pattern]) -> Pattern:
        return pattern.instantiate(delta)

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


@dataclass
class Claim:
    pattern: Pattern


class StatefulInterpreter(BasicInterpreter):
    """A Proof interpreter that also keeps track of the verifier state,
    such as the memory, stack and claims remaining.
    """

    claims: list[Claim]
    stack: list[Pattern | Proved]
    memory: list[Pattern | Proved]

    def __init__(
        self, phase: ExecutionPhase, claims: list[Claim] | None = None, axioms: list[Pattern] | None = None
    ) -> None:
        super().__init__(phase=phase)
        self.stack = []
        self.memory = []
        self.claims = claims if claims else []

        if phase == ExecutionPhase.Proof:
            raw_terms = axioms if axioms else []
            self.memory = list(map(partial(Proved, self), raw_terms))

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

    def symbol(self, id: int) -> Pattern:
        ret = super().symbol(id)
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

    def pattern(self, pattern: Pattern) -> Pattern:
        if pattern in self.memory:
            self.load('', pattern)
            return pattern
        return super().pattern(pattern)

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

    def instantiate(self, proved: Proved, delta: dict[int, Pattern]) -> Proved:
        expected_plugs = self.stack[-len(delta) :]
        *self.stack, expected_proved = self.stack[0 : -len(delta)]
        assert expected_proved == proved, f'expected: {expected_proved}\ngot: {proved}'
        assert expected_plugs == list(delta.values()), f'expected: {expected_plugs}\ngot: {list(delta.values())}'
        ret = super().instantiate(proved, delta)
        self.stack.append(ret)
        return ret

    def instantiate_notation(self, pattern: Pattern, delta: dict[int, Pattern]) -> Pattern:
        expected_plugs = self.stack[-len(delta) :]
        *self.stack, expected_pattern = self.stack[0 : -len(delta)]
        assert expected_pattern == pattern, f'expected: {expected_pattern}\ngot: {pattern}'
        assert expected_plugs == list(delta.values()), f'expected: {expected_plugs}\ngot: {list(delta.values())}'
        ret = super().instantiate_notation(pattern, delta)
        self.stack.append(ret)
        return ret

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
        assert proved.conclusion == expected_claim.pattern, f'{proved.conclusion, expected_claim.pattern}'
        assert self.stack[-1] == proved

    def publish_axiom(self, axiom: Pattern) -> None:
        super().publish_axiom(axiom)
        assert self.stack[-1] == axiom

    def publish_claim(self, pattern: Pattern) -> None:
        super().publish_claim(pattern)
        expected_claim, *self.claims = self.claims
        # assert expected_claim.pattern == pattern, 'expected: {}\ngot: {}'.format(expected_claim.pattern, pattern)
        assert self.stack[-1] == pattern


class SerializingInterpreter(StatefulInterpreter):
    def __init__(
        self,
        phase: ExecutionPhase,
        out: BinaryIO,
        claims: list[Claim] | None = None,
        axioms: list[Pattern] | None = None,
    ) -> None:
        super().__init__(phase=phase, claims=claims, axioms=axioms)
        self.out = out

    def evar(self, id: int) -> Pattern:
        ret = super().evar(id)
        self.out.write(bytes([Instruction.EVar, id]))
        return ret

    def svar(self, id: int) -> Pattern:
        ret = super().svar(id)
        self.out.write(bytes([Instruction.SVar, id]))
        return ret

    def symbol(self, id: int) -> Pattern:
        ret = super().symbol(id)
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
        for list in lists:
            self.out.write(bytes([Instruction.List, len(list), *[var.name for var in list]]))
        self.out.write(bytes([Instruction.MetaVar, id]))
        return ret

    def implies(self, left: Pattern, right: Pattern) -> Pattern:
        ret = super().implies(left, right)
        self.out.write(bytes([Instruction.Implication]))
        return ret

    def app(self, left: Pattern, right: Pattern) -> Pattern:
        ret = super().app(left, right)
        self.out.write(bytes([Instruction.Application]))
        return ret

    def exists(self, var: int, subpattern: Pattern) -> Pattern:
        ret = super().exists(var, subpattern)
        self.out.write(bytes([Instruction.Exists, var]))
        return ret

    def mu(self, var: int, subpattern: Pattern) -> Pattern:
        ret = super().mu(var, subpattern)
        self.out.write(bytes([Instruction.Mu, var]))
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

    def instantiate(self, proved: Proved, delta: dict[int, Pattern]) -> Proved:
        ret = super().instantiate(proved, delta)
        self.out.write(bytes([Instruction.Instantiate, len(delta), *reversed(delta.keys())]))
        return ret

    def instantiate_notation(self, pattern: Pattern, delta: dict[int, Pattern]) -> Pattern:
        ret = super().instantiate_notation(pattern, delta)
        self.out.write(bytes([Instruction.Instantiate, len(delta), *reversed(delta.keys())]))
        return ret

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


class PrettyPrintingInterpreter(StatefulInterpreter):
    def __init__(
        self, phase: ExecutionPhase, out: TextIO, claims: list[Claim] | None = None, axioms: list[Pattern] | None = None
    ) -> None:
        super().__init__(phase=phase, claims=claims, axioms=axioms)
        self.out = out
        self._notation: dict[str, Pattern] = {}

    def plug_in_notation(self, notation: dict[str, Pattern]) -> None:
        self._notation = notation

    @property
    def notation(self) -> dict[Pattern, str]:
        return {v: k for k, v in self._notation.items()}

    @staticmethod
    def pretty(print_stack: bool = True) -> Callable:
        def decorator(func: Callable) -> Callable:
            def wrapper(*args: Pattern | dict | PrettyPrintingInterpreter, **kwargs: dict) -> Pattern | Proved:
                self, *nargs = args
                assert isinstance(self, PrettyPrintingInterpreter)
                # Find and call the super method.
                result = getattr(super(PrettyPrintingInterpreter, self), func.__name__)(*nargs, **kwargs)
                # Call the pretty printing function.
                func(self, *nargs, **kwargs)
                self.out.write('\n')
                # Print stack
                if print_stack:
                    self.print_stack()
                return result

            return wrapper

        return decorator

    @pretty()
    def evar(self, id: int) -> None:
        self.out.write('EVar ')
        self.out.write(str(id))

    @pretty()
    def svar(self, id: int) -> None:
        self.out.write('SVar ')
        self.out.write(str(id))

    @pretty()
    def symbol(self, id: int) -> None:
        self.out.write('Symbol ')
        self.out.write(str(id))

    @pretty(print_stack=False)
    def metavar(
        self,
        id: int,
        e_fresh: tuple[EVar, ...] = (),
        s_fresh: tuple[SVar, ...] = (),
        positive: tuple[SVar, ...] = (),
        negative: tuple[SVar, ...] = (),
        application_context: tuple[EVar, ...] = (),
    ) -> None:
        def write_list(name: str, lst: tuple[EVar, ...] | tuple[SVar, ...]) -> None:
            self.out.write(f'List={name} ')
            self.out.write(f'len={len(lst)} ')
            for item in lst:
                self.out.write(str(item))
                self.out.write(' ')
            self.out.write('\n')

        write_list('eFresh', e_fresh)
        write_list('sFresh', s_fresh)
        write_list('pos', positive)
        write_list('neg', negative)
        write_list('appctx', application_context)
        self.out.write('MetaVar ')
        self.out.write(str(id))

    @pretty()
    def implies(self, left: Pattern, right: Pattern) -> None:
        self.out.write('Implication')

    @pretty()
    def app(self, left: Pattern, right: Pattern) -> None:
        self.out.write('Application')

    @pretty()
    def exists(self, var: int, subpattern: Pattern) -> None:
        self.out.write('Exists ')
        self.out.write(str(var))

    @pretty()
    def mu(self, var: int, subpattern: Pattern) -> None:
        self.out.write('Mu ')
        self.out.write(str(var))

    @pretty()
    def prop1(self) -> None:
        self.out.write('Prop1')

    @pretty()
    def prop2(self) -> None:
        self.out.write('Prop2')

    @pretty()
    def prop3(self) -> None:
        self.out.write('Prop3')

    @pretty()
    def modus_ponens(self, left: Proved, right: Proved) -> None:
        self.out.write('ModusPonens')

    @pretty()
    def instantiate(self, proved: Proved, delta: dict[int, Pattern]) -> None:
        self.out.write('Instantiate ')
        self.out.write(', '.join(map(str, delta.keys())))

    @pretty()
    def instantiate_notation(self, pattern: Pattern, delta: dict[int, Pattern]) -> None:
        self.out.write('Instantiate ')
        self.out.write(', '.join(map(str, delta.keys())))

    @pretty(print_stack=False)
    def save(self, id: str, term: Pattern | Proved) -> None:
        self.out.write('Save')

    @pretty()
    def load(self, id: str, term: Pattern | Proved) -> None:
        self.out.write('Load ')
        self.out.write(id)
        self.out.write('=')
        self.out.write(str(self.memory.index(term)))

    @pretty()
    def publish_proof(self, proved: Proved) -> None:
        self.out.write('Publish')

    @pretty()
    def publish_axiom(self, axiom: Pattern) -> None:
        self.out.write('Publish')

    @pretty()
    def publish_claim(self, pattern: Pattern) -> None:
        self.out.write('Publish')

    def pretty_print_pattern(self, p: Pattern) -> str:
        if p in self.notation:
            return self.notation[p]

        # TODO: Figure out how to avoid this "double" definition of pretty printing for some cases
        # like implication while keeping notations
        match p:
            case Implication(left, right):
                return f'({self.pretty_print_pattern(left)} -> {self.pretty_print_pattern(right)})'
            case Application(left, right):
                return f'(app ({self.pretty_print_pattern(left)}) ({self.pretty_print_pattern(right)}))'
            case Exists(var, subpattern):
                return f'(\u2203 {str(var)} . {self.pretty_print_pattern(subpattern)})'
            case Mu(var, subpattern):
                return f'(\u03BC {self.pretty_print_pattern(var)} . {self.pretty_print_pattern(p.subpattern)})'
            case ESubst(pattern, var, plug):
                return f'({self.pretty_print_pattern(pattern)}[{self.pretty_print_pattern(plug)}/{str(var)}])'
            case SSubst(pattern, var, plug):
                return f'({self.pretty_print_pattern(pattern)}[{self.pretty_print_pattern(plug)}/{str(var)}])'
        return str(p)

    def print_stack(self) -> None:
        self.out.write('\tStack:\n')
        for i, item in enumerate(reversed(self.stack)):
            if isinstance(item, Proved):
                item = item.conclusion
            self.out.write(f'\t{i}: {self.pretty_print_pattern(item)}\n')


class NotationlessPrettyPrinter(PrettyPrintingInterpreter):
    def save(self, id: str, term: Pattern | Proved) -> None:
        id = str(len(self.memory))
        ret = super().save(id, term)
        return ret

    def load(self, id: str, term: Pattern | Proved) -> None:
        id = str(self.memory.index(term))
        ret = super().load(id, term)
        return ret


PatternExpression = Callable[[], Pattern]
ProvedExpression = Callable[[], Proved]


class ProofExp:
    interpreter: BasicInterpreter

    def __init__(self, interpreter: BasicInterpreter) -> None:
        self.interpreter = interpreter
        self.notation: dict[str, Pattern] = {}

    @staticmethod
    def axioms() -> list[Pattern]:
        raise NotImplementedError

    @staticmethod
    def claims() -> list[Pattern]:
        raise NotImplementedError

    def claim_expressions(self) -> list[PatternExpression]:
        raise NotImplementedError

    def proof_expressions(self) -> list[ProvedExpression]:
        raise NotImplementedError

    # Patterns
    # ========

    def svar(self, id: int) -> Pattern:
        return self.interpreter.svar(id)

    def evar(self, id: int) -> Pattern:
        return self.interpreter.evar(id)

    def symbol(self, id: int) -> Pattern:
        return self.interpreter.symbol(id)

    def implies(self, left: Pattern, right: Pattern) -> Pattern:
        return self.interpreter.implies(left, right)

    def app(self, left: Pattern, right: Pattern) -> Pattern:
        return self.interpreter.app(left, right)

    def exists(self, var: int, subpattern: Pattern) -> Pattern:
        return self.interpreter.exists(var, subpattern)

    def mu(self, var: int, subpattern: Pattern) -> Pattern:
        return self.interpreter.mu(var, subpattern)

    def metavar(
        self,
        name: int,
        e_fresh: tuple[EVar, ...] = (),
        s_fresh: tuple[SVar, ...] = (),
        positive: tuple[SVar, ...] = (),
        negative: tuple[SVar, ...] = (),
        application_context: tuple[EVar, ...] = (),
    ) -> Pattern:
        return self.interpreter.metavar(name, e_fresh, s_fresh, positive, negative, application_context)

    # Proof Rules
    # -----------

    def prop1(self) -> Proved:
        return self.interpreter.prop1()

    def prop2(self) -> Proved:
        return self.interpreter.prop2()

    def prop3(self) -> Proved:
        return self.interpreter.prop3()

    def modus_ponens(self, left: Proved, right: Proved) -> Proved:
        return self.interpreter.modus_ponens(left, right)

    def instantiate(self, proved: Proved, delta: dict[int, Pattern]) -> Proved:
        return self.interpreter.instantiate(proved, delta)

    def instantiate_notation(self, pattern: Pattern, delta: dict[int, Pattern]) -> Pattern:
        return self.interpreter.instantiate_notation(pattern, delta)

    def load_notation(self, id: str) -> Pattern | None:
        if id not in self.notation:
            return None
        ret = self.notation[id]
        self.interpreter.load(id, ret)
        return ret

    def load_axiom(self, axiom_term: Pattern) -> Proved:
        assert axiom_term in self.axioms()
        axiom = Proved(self.interpreter, axiom_term)
        assert axiom in self.interpreter.memory  # type: ignore
        axiom_index = self.interpreter.memory.index(axiom)  # type: ignore
        self.interpreter.load(str(axiom_index), axiom)
        return axiom

    def save_notation(self, id: str, pattern: Pattern) -> Pattern:
        assert id not in self.notation
        self.notation[id] = pattern
        self.interpreter.save(id, pattern)
        return pattern

    def save_pattern(self, id: str, pattern: Pattern) -> Pattern:
        self.interpreter.save(id, pattern)
        return pattern

    def publish_axiom(self, proved: Pattern) -> Pattern:
        self.interpreter.publish_axiom(proved)
        return proved

    def publish_proof(self, proved: Proved) -> Proved:
        self.interpreter.publish_proof(proved)
        return proved

    def publish_claim(self, pattern: Pattern) -> Pattern:
        self.interpreter.publish_claim(pattern)
        return pattern

    @classmethod
    def serialize_claims(cls, output: Path) -> None:
        with open(output, 'wb') as out:
            claims = list(map(Claim, cls.claims()))
            proof_exp = cls(SerializingInterpreter(phase=ExecutionPhase.Claim, claims=claims, out=out))
            for claim_expr in reversed(proof_exp.claims()):
                proof_exp.publish_claim(proof_exp.interpreter.pattern(claim_expr))

    @classmethod
    def serialize_proofs(cls, output: Path) -> None:
        with open(output, 'wb') as out:
            claims = list(map(Claim, cls.claims()))
            proof_exp = cls(
                SerializingInterpreter(phase=ExecutionPhase.Proof, claims=claims, axioms=cls.axioms(), out=out)
            )
            for proof_expr in proof_exp.proof_expressions():
                proof_exp.publish_proof(proof_expr())

    @classmethod
    def serialize_gamma(cls, output: Path) -> None:
        with open(output, 'wb') as out:
            claims = list(map(Claim, cls.claims()))
            proof_exp = cls(SerializingInterpreter(phase=ExecutionPhase.Gamma, claims=claims, out=out))
            for axiom in proof_exp.axioms():
                proof_exp.publish_axiom(proof_exp.interpreter.pattern(axiom))

    @classmethod
    def pretty_print_gamma(cls, output: Path) -> None:
        with open(output, 'w') as out:
            claims = list(map(Claim, cls.claims()))
            interpreter = PrettyPrintingInterpreter(phase=ExecutionPhase.Gamma, claims=claims, out=out)
            proof_exp = cls(interpreter)
            # TODO: A bit ugly
            interpreter.plug_in_notation(proof_exp.notation)
            for axiom in proof_exp.axioms():
                proof_exp.publish_axiom(proof_exp.interpreter.pattern(axiom))

    @classmethod
    def pretty_print_claims(cls, output: Path) -> None:
        with open(output, 'w') as out:
            claims = list(map(Claim, cls.claims()))
            interpreter = PrettyPrintingInterpreter(phase=ExecutionPhase.Claim, claims=claims, out=out)
            proof_exp = cls(interpreter)
            # TODO: A bit ugly
            interpreter.plug_in_notation(proof_exp.notation)
            for claim_expr in reversed(proof_exp.claims()):
                proof_exp.publish_claim(proof_exp.interpreter.pattern(claim_expr))

    @classmethod
    def pretty_print_proofs(cls, output: Path) -> None:
        with open(output, 'w') as out:
            claims = list(map(Claim, cls.claims()))
            interpreter = PrettyPrintingInterpreter(
                phase=ExecutionPhase.Proof, claims=claims, axioms=cls.axioms(), out=out
            )
            proof_exp = cls(interpreter)
            # TODO: A bit ugly
            interpreter.plug_in_notation(proof_exp.notation)
            for proof_expr in proof_exp.proof_expressions():
                proof_exp.publish_proof(proof_expr())

    @classmethod
    def main(cls, argv: list[str]) -> None:
        exe, *argv = argv
        usage = f'Usage:\n\n python3 {exe} (binary|pretty) (claim|proof) output-file\n python3 {exe} --help\n\n'
        examples = (
            f'Examples:\n\npython3 {exe} binary claim a.out\n# outputs claims of ProofExp object in verifier-checkable binary format to file a.out\n\n'
            + f'python3 {exe} pretty claim /dev/stdout\n# outputs claims of ProofExp object in human-readable format to standard output\n'
        )

        if len(argv) == 1:
            assert argv[0] == '--help', usage
            print(usage + examples)
            return

        assert len(argv) == 3, usage
        format, mode, output_path = argv

        match (format, mode):
            case ('pretty', 'claim'):
                cls.pretty_print_claims(Path(output_path))
            case ('pretty', 'proof'):
                cls.pretty_print_proofs(Path(output_path))
            case ('binary', 'claim'):
                cls.serialize_claims(Path(output_path))
            case ('binary', 'proof'):
                cls.serialize_proofs(Path(output_path))
            case ('binary', 'gamma'):
                cls.serialize_gamma(Path(output_path))
            case ('pretty', 'gamma'):
                cls.pretty_print_gamma(Path(output_path))
            case _:
                raise AssertionError(usage)
