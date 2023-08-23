from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass
from pathlib import Path
from typing import BinaryIO, TextIO

from proof_generation.instruction import Instruction


class Term:
    ...


class Pattern(Term):
    def instantiate(self, delta: dict[int, Pattern]) -> Pattern:
        raise NotImplementedError


@dataclass(frozen=True)
class EVar(Pattern):
    name: int

    @classmethod
    def shorthand(cls) -> dict[str, str]:
        return {'name': ''}

    def instantiate(self, delta: dict[int, Pattern]) -> Pattern:
        return self


@dataclass(frozen=True)
class SVar(Pattern):
    name: int

    @classmethod
    def shorthand(cls) -> dict[str, str]:
        return {'name': ''}

    def instantiate(self, delta: dict[int, Pattern]) -> Pattern:
        return self


@dataclass(frozen=True)
class Symbol(Pattern):
    name: int

    def instantiate(self, delta: dict[int, Pattern]) -> Pattern:
        return self


@dataclass(frozen=True)
class Implication(Pattern):
    left: Pattern
    right: Pattern

    @classmethod
    def shorthand(cls) -> dict[str, str]:
        return {'__name__': 'Imp', 'left': '', 'right': ''}

    def instantiate(self, delta: dict[int, Pattern]) -> Pattern:
        return Implication(self.left.instantiate(delta), self.right.instantiate(delta))


@dataclass(frozen=True)
class Application(Pattern):
    left: Pattern
    right: Pattern

    def instantiate(self, delta: dict[int, Pattern]) -> Pattern:
        return Application(self.left.instantiate(delta), self.right.instantiate(delta))


@dataclass(frozen=True)
class Exists(Pattern):
    var: EVar
    subpattern: Pattern

    @classmethod
    def shorthand(cls) -> dict[str, str]:
        return {'__name__': '\u2203', 'var': '', 'subpattern': ''}

    def instantiate(self, delta: dict[int, Pattern]) -> Pattern:
        return Exists(self.var, self.subpattern.instantiate(delta))


@dataclass(frozen=True)
class Mu(Pattern):
    var: SVar
    subpattern: Pattern

    @classmethod
    def shorthand(cls) -> dict[str, str]:
        return {
            '__name__': '\u03BC',
            'var': '',
            'subpattern': '',
        }

    def instantiate(self, delta: dict[int, Pattern]) -> Pattern:
        return Mu(self.var, self.subpattern.instantiate(delta))


@dataclass(frozen=True)
class MetaVar(Pattern):
    name: int
    e_fresh: tuple[EVar, ...] = ()
    s_fresh: tuple[SVar, ...] = ()
    positive: tuple[SVar, ...] = ()
    negative: tuple[SVar, ...] = ()
    app_ctx_holes: tuple[EVar, ...] = ()

    @classmethod
    def shorthand(cls) -> dict[str, str]:
        return {
            '__name__': 'MV',
            'name': '',
            'e_fresh': 'e_f',
            's_fresh': 's_f',
            'positive': 'pos',
            'negative': 'neg',
            'application_context': 'app_cntxt',
        }

    def instantiate(self, delta: dict[int, Pattern]) -> Pattern:
        if self.name in delta:
            return delta[self.name]
        return self


@dataclass(frozen=True)
class ESubst(Pattern):
    pattern: MetaVar
    var: EVar
    plug: Pattern


@dataclass(frozen=True)
class SSubst(Pattern):
    pattern: MetaVar
    var: SVar
    plug: Pattern


@dataclass
class Proved:
    interpreter: BasicInterpreter
    conclusion: Pattern

    def instantiate(self: Proved, delta: dict[int, Pattern]) -> Proved:
        return self.interpreter.instantiate(self, delta)

    def assertc(self, pattern: Pattern) -> Proved:
        assert self.conclusion == pattern
        return self


# Proof Expressions
# =================


class BasicInterpreter:
    """A stateless proof interpreter. It only checks conclusions."""

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

    def load(self, id: str) -> None:
        ...

    def publish(self, term: Proved) -> None:
        ...

    def publish_claim(self, term: Pattern) -> None:
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
    memory: dict[str, Pattern | Proved]

    def __init__(self, claims: list[Claim]) -> None:
        super().__init__()
        self.stack = []
        self.memory = {}
        self.claims = claims

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
        for pat in delta.values():
            self.walk(pat)

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
        self.memory[id] = term
        super().save(id, term)

    def load(self, id: str) -> None:
        assert id in self.memory
        self.stack.append(self.memory[id])
        super().load(id)

    def publish(self, proved: Proved) -> None:
        # TODO: This should only be enabled in the claims proofs phase.
        super().publish(proved)
        expected_claim, *self.claims = self.claims
        assert proved.conclusion == expected_claim.pattern
        assert self.stack[-1] == proved

    def publish_claim(self, pattern: Pattern) -> None:
        # TODO: This should only be enabled in the claims phase.
        super().publish_claim(pattern)
        expected_claim, *self.claims = self.claims
        # assert expected_claim.pattern == pattern, 'expected: {}\ngot: {}'.format(expected_claim.pattern, pattern)
        assert self.stack[-1] == pattern

    def walk(self, p: Pattern) -> Pattern:
        match p:
            case EVar(name):
                return self.evar(name)
            case SVar(name):
                return self.svar(name)
            case Symbol(name):
                return self.symbol(name)
            case Implication(left, right):
                return self.implies(self.walk(left), self.walk(right))
            case Application(left, right):
                return self.app(self.walk(left), self.walk(right))
            case Exists(var, subpattern):
                return self.exists(var.name, self.walk(subpattern))
            case Mu(var, subpattern):
                return self.mu(var.name, self.walk(subpattern))
            case MetaVar(name, e_fresh, s_fresh, positive, negative, app_ctx_holes):
                # TODO: Walking through the variables (so that they are on stack)
                return self.metavar(name, e_fresh, s_fresh, positive, negative, app_ctx_holes)
        return p

    # TODO: p will be memoized, so that it can be reused with load/save
    # TODO: memo will also be able to "build up the term" in a serializable
    # manner to fix those issues with instantiations
    def memo(self, p: Pattern) -> Pattern:
        if p in self.memoization:
            self.load(self.memoization[p])
        else:
            self.walk(p)
            self.memoization[p] = str(len(self.memory))
            self.save(self.memoization[p], p)
        return p

    # TODO: Use some type-narrowing to do this
    def memo2(self, p: Proved) -> Proved:
        self.stack.append(p)
        return p


class SerializingInterpreter(StatefulInterpreter):
    def __init__(self, claims: list[Claim], out: BinaryIO) -> None:
        super().__init__(claims)
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
        super().save(id, term)
        self.out.write(bytes([Instruction.Save]))

    def load(self, id: str) -> None:
        super().load(id)
        self.out.write(bytes([Instruction.Load, list(self.memory.values()).index(self.memory[id])]))

    def publish(self, proved: Proved) -> None:
        super().publish(proved)
        self.out.write(bytes([Instruction.Publish]))

    def publish_claim(self, pattern: Pattern) -> None:
        super().publish_claim(pattern)
        self.out.write(bytes([Instruction.Publish]))


class PrettyPrintingInterpreter(StatefulInterpreter):
    def __init__(self, claims: list[Claim], out: TextIO) -> None:
        super().__init__(claims)
        self.out = out

    def evar(self, id: int) -> Pattern:
        ret = super().evar(id)
        self.out.write('EVar ')
        self.out.write(str(id))
        self.out.write('\n')
        return ret

    def svar(self, id: int) -> Pattern:
        ret = super().svar(id)
        self.out.write('SVar ')
        self.out.write(str(id))
        self.out.write('\n')
        return ret

    def symbol(self, id: int) -> Pattern:
        ret = super().symbol(id)
        self.out.write('Symbol ')
        self.out.write(str(id))
        self.out.write('\n')
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
        def write_list(name: str, l: tuple[EVar, ...] | tuple[SVar, ...]) -> None:
            self.out.write(f'List={name} ')
            self.out.write(f'len={len(l)} ')
            for item in l:
                self.out.write(str(item))
                self.out.write(' ')
            self.out.write('\n')

        ret = super().metavar(id, e_fresh, s_fresh, positive, negative, application_context)
        write_list('eFresh', e_fresh)
        write_list('sFresh', s_fresh)
        write_list('pos', positive)
        write_list('neg', negative)
        write_list('appctx', application_context)
        self.out.write('MetaVar ')
        self.out.write(str(id))
        self.out.write('\n')
        return ret

    def implies(self, left: Pattern, right: Pattern) -> Pattern:
        ret = super().implies(left, right)
        self.out.write('Implication')
        self.out.write('\n')
        return ret

    def app(self, left: Pattern, right: Pattern) -> Pattern:
        ret = super().app(left, right)
        self.out.write('Application')
        self.out.write('\n')
        return ret

    def exists(self, var: int, subpattern: Pattern) -> Pattern:
        ret = super().exists(var, subpattern)
        self.out.write('Exists ')
        self.out.write(str(var))
        self.out.write('\n')
        return ret

    def mu(self, var: int, subpattern: Pattern) -> Pattern:
        ret = super().mu(var, subpattern)
        self.out.write('Mu ')
        self.out.write(str(var))
        self.out.write('\n')
        return ret

    def prop1(self) -> Proved:
        ret = super().prop1()
        self.out.write('Prop1')
        self.out.write('\n')
        return ret

    def prop2(self) -> Proved:
        ret = super().prop2()
        self.out.write('Prop2')
        self.out.write('\n')
        return ret

    def prop3(self) -> Proved:
        ret = super().prop3()
        self.out.write('Prop3')
        self.out.write('\n')
        return ret

    def modus_ponens(self, left: Proved, right: Proved) -> Proved:
        ret = super().modus_ponens(left, right)
        self.out.write('ModusPonens')
        self.out.write('\n')
        return ret

    def instantiate(self, proved: Proved, delta: dict[int, Pattern]) -> Proved:
        ret = super().instantiate(proved, delta)
        self.out.write('Instantiate ')
        self.out.write(', '.join(map(str, delta.keys())))
        self.out.write('\n')
        return ret

    def instantiate_notation(self, pattern: Pattern, delta: dict[int, Pattern]) -> Pattern:
        ret = super().instantiate_notation(pattern, delta)
        self.out.write('Instantiate ')
        self.out.write(', '.join(map(str, delta.keys())))
        self.out.write('\n')
        return ret

    def save(self, id: str, term: Pattern | Proved) -> None:
        super().save(id, term)
        self.out.write('Save // ')
        self.out.write(id)
        self.out.write('=')
        self.out.write(str(term))
        self.out.write('\n')

    def load(self, id: str) -> None:
        super().load(id)
        self.out.write('Load ')
        self.out.write(str(list(self.memory.values()).index(self.memory[id])))
        self.out.write(' // ')
        self.out.write(id)
        self.out.write('=')
        self.out.write(str(self.memory[id]))
        self.out.write('\n')

    def publish(self, proved: Proved) -> None:
        super().publish(proved)
        self.out.write('Publish\n')

    def publish_claim(self, pattern: Pattern) -> None:
        super().publish_claim(pattern)
        self.out.write('Publish\n')


PatternExpression = Callable[[], Pattern]
ProvedExpression = Callable[[], Proved]


class ProofExp:
    interpreter: StatefulInterpreter

    def __init__(self, interpreter: StatefulInterpreter) -> None:
        self.interpreter = interpreter
        self.memoization: dict[Pattern, str] = {}

    @staticmethod
    def claims() -> list[Pattern]:
        raise NotImplementedError

    def claim_expressions(self) -> list[PatternExpression]:
        raise NotImplementedError

    def proof_expressions(self) -> list[ProvedExpression]:
        raise NotImplementedError

    def walk(self, p: Pattern) -> Pattern:
        match p:
            case EVar(name):
                return self.evar(name)
            case SVar(name):
                return self.svar(name)
            case Symbol(name):
                return self.symbol(name)
            case Implication(left, right):
                return self.implies(self.walk(left), self.walk(right))
            case Application(left, right):
                return self.app(self.walk(left), self.walk(right))
            case Exists(var, subpattern):
                return self.exists(var.name, self.walk(subpattern))
            case Mu(var, subpattern):
                return self.mu(var.name, self.walk(subpattern))
            case MetaVar(name, e_fresh, s_fresh, positive, negative, app_ctx_holes):
                # TODO: Walking through the variables (so that they are on stack)
                return self.metavar(name, e_fresh, s_fresh, positive, negative, app_ctx_holes)
        return p

    # TODO: p will be memoized, so that it can be reused with load/save
    # TODO: memo will also be able to "build up the term" in a serializable
    # manner to fix those issues with instantiations
    def memo(self, p: Pattern) -> Pattern:
        if p in self.memoization:
            self.interpreter.load(self.memoization[p])
        else:
            self.walk(p)
            self.memoization[p] = str(len(self.interpreter.memory))
            self.interpreter.save(self.memoization[p], p)
        return p

    # TODO: Use some type-narrowing to do this
    def memo2(self, p: Proved) -> Proved:
        self.interpreter.stack.append(p)
        return p

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

    # TODO: Instantiate will use memo automatically for all Patterns
    def instantiate(self, proved: Proved, delta: dict[int, Pattern]) -> Proved:
        return self.interpreter.instantiate(proved, delta)

    def instantiate_memo(self, proved: Proved, delta: dict[int, Pattern]) -> Proved:
        for pat in delta.values():
            self.memo(pat)

        return self.interpreter.instantiate(proved, delta)

    def instantiate_notation(self, pattern: Pattern, delta: dict[int, Pattern]) -> Pattern:
        return self.interpreter.instantiate_notation(pattern, delta)

    def load_notation(self, id: str) -> Pattern | None:
        if id not in self.interpreter.memory:
            return None
        ret = self.interpreter.memory[id]
        assert isinstance(ret, Pattern)
        self.interpreter.load(id)
        return ret

    def save_notation(self, id: str, pattern: Pattern) -> Pattern:
        assert id not in self.interpreter.memory
        self.interpreter.memory[id] = pattern
        self.interpreter.save(id, pattern)
        return pattern

    def save_pattern(self, id: str, pattern: Pattern) -> Pattern:
        self.interpreter.save(id, pattern)
        return pattern

    def publish(self, proved: Proved) -> Proved:
        self.interpreter.publish(proved)
        return proved

    def publish_claim(self, pattern: Pattern) -> Pattern:
        self.interpreter.publish_claim(pattern)
        return pattern

    @classmethod
    def serialize_claims(cls, output: Path) -> None:
        with open(output, 'wb') as out:
            claims = list(map(Claim, cls.claims()))
            proof_exp = cls(SerializingInterpreter(claims=claims, out=out))
            for claim_expr in reversed(proof_exp.claim_expressions()):
                proof_exp.publish_claim(claim_expr())

    @classmethod
    def serialize_proofs(cls, output: Path) -> None:
        with open(output, 'wb') as out:
            claims = list(map(Claim, cls.claims()))
            interpreter = SerializingInterpreter(claims=claims, out=out)
            proof_exp = cls(interpreter)
            for proof_expr in proof_exp.proof_expressions():
                proof_exp.publish(proof_expr(interpreter))

    @classmethod
    def pretty_print_claims(cls, output: Path) -> None:
        with open(output, 'w') as out:
            claims = list(map(Claim, cls.claims()))
            proof_exp = cls(PrettyPrintingInterpreter(claims=claims, out=out))
            for claim_expr in reversed(proof_exp.claim_expressions()):
                proof_exp.publish_claim(claim_expr())

    @classmethod
    def pretty_print_proofs(cls, output: Path) -> None:
        with open(output, 'w') as out:
            claims = list(map(Claim, cls.claims()))
            interpreter = PrettyPrintingInterpreter(claims=claims, out=out)
            proof_exp = cls(interpreter)
            for proof_expr in proof_exp.proof_expressions():
                proof_exp.publish(proof_expr(interpreter))

    @classmethod
    def main(cls, argv: list[str]) -> None:
        usage = 'Usage: {} binary|pretty claim|proof output-file'
        assert len(argv) == 4, usage
        _exe, format, mode, output_path = argv

        match (format, mode):
            case ('pretty', 'claim'):
                cls.pretty_print_claims(Path(output_path))
            case ('pretty', 'proof'):
                cls.pretty_print_proofs(Path(output_path))
            case ('binary', 'claim'):
                cls.serialize_claims(Path(output_path))
            case ('binary', 'proof'):
                cls.serialize_proofs(Path(output_path))
            case _:
                raise AssertionError(usage)
