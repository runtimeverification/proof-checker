from __future__ import annotations

from dataclasses import dataclass
from typing import BinaryIO

from proof_generation.instruction import Instruction


class Term:
    ...

    def serialize(self, to_reuse: set[Term], memory: list[Term], output: BinaryIO) -> None:
        if self in memory:
            output.write(bytes([Instruction.Load, memory.index(self)]))
            return
        self.serialize_impl(to_reuse, memory, output)
        if self in to_reuse:
            memory.append(self)
            output.write(bytes([Instruction.Save]))

    def serialize_impl(self, to_reuse: set[Term], memory: list[Term], output: BinaryIO) -> None:
        raise NotImplementedError


class Pattern(Term):
    def instantiate(self, var: int, plug: Pattern) -> Pattern:
        raise NotImplementedError


@dataclass(frozen=True)
class EVar(Pattern):
    name: int


@dataclass(frozen=True)
class SVar(Pattern):
    name: int


@dataclass(frozen=True)
class Symbol(Pattern):
    name: int


@dataclass(frozen=True)
class Implication(Pattern):
    left: Pattern
    right: Pattern

    def serialize_impl(self, to_reuse: set[Term], memory: list[Term], output: BinaryIO) -> None:
        self.left.serialize(to_reuse, memory, output)
        self.right.serialize(to_reuse, memory, output)
        output.write(bytes([Instruction.Implication]))

    def instantiate(self, var: int, plug: Pattern) -> Pattern:
        return Implication(self.left.instantiate(var, plug), self.right.instantiate(var, plug))


@dataclass(frozen=True)
class Application(Pattern):
    left: Pattern
    right: Pattern

    def instantiate(self, var: int, plug: Pattern) -> Pattern:
        return Application(self.left.instantiate(var, plug), self.right.instantiate(var, plug))


@dataclass(frozen=True)
class Exists(Pattern):
    var: EVar
    subpattern: Pattern

    def instantiate(self, var: int, plug: Pattern) -> Pattern:
        return Exists(self.var, self.subpattern.instantiate(var, plug))


@dataclass(frozen=True)
class Mu(Pattern):
    var: SVar
    subpattern: Pattern

    def instantiate(self, var: int, plug: Pattern) -> Pattern:
        return Mu(self.var, self.subpattern.instantiate(var, plug))


@dataclass(frozen=True)
class MetaVar(Pattern):
    name: int
    e_fresh: tuple[EVar, ...] = ()
    s_fresh: tuple[SVar, ...] = ()
    positive: tuple[SVar, ...] = ()
    negative: tuple[SVar, ...] = ()
    application_context: tuple[EVar, ...] = ()

    def serialize_impl(self, to_reuse: set[Term], memory: list[Term], output: BinaryIO) -> None:
        lists: list[tuple[EVar, ...] | tuple[SVar, ...]] = [
            self.e_fresh,
            self.s_fresh,
            self.positive,
            self.negative,
            self.application_context,
        ]
        for list in lists:
            output.write(bytes([Instruction.List, len(list), *[var.name for var in list]]))
        output.write(bytes([Instruction.MetaVar, self.name]))

    def instantiate(self, var: int, plug: Pattern) -> Pattern:
        if var == self.name:
            return plug
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


# Shortcuts and Sugar
# ===================


def implies(left: Pattern, right: Pattern) -> Pattern:
    return Implication(left, right)


def app(left: Pattern, right: Pattern) -> Pattern:
    return Application(left, right)


def exists(var: int, subpattern: Pattern) -> Pattern:
    return Exists(EVar(var), subpattern)

def mu(var: int, subpattern: Pattern) -> Pattern:
    return Mu(SVar(var), subpattern)


X = SVar(0)
bot = Mu(X, X)


def neg(p: Pattern) -> Pattern:
    return implies(p, bot)


# Proofs
# ======


@dataclass(frozen=True)
class Proof(Term):
    def instantiate(self: Proof, var: int, plug: Pattern) -> Proof:
        return Instantiate(self, var, plug)

    def conclusion(self) -> Pattern:
        raise NotImplementedError


@dataclass(frozen=True)
class Instantiate(Proof):
    subproof: Proof
    var: int
    plug: Pattern

    def well_formed(self) -> bool:
        return True

    def serialize_impl(self, to_reuse: set[Term], memory: list[Term], output: BinaryIO) -> None:
        self.subproof.serialize(to_reuse, memory, output)
        self.plug.serialize(to_reuse, memory, output)
        output.write(bytes([Instruction.Instantiate, self.var]))

    def conclusion(self) -> Pattern:
        return self.subproof.conclusion().instantiate(self.var, self.plug)


@dataclass(frozen=True)
class ModusPonens(Proof):
    left: Proof
    right: Proof
    ...

    def serialize_impl(self, to_reuse: set[Term], memory: list[Term], output: BinaryIO) -> None:
        self.left.serialize(to_reuse, memory, output)
        self.right.serialize(to_reuse, memory, output)
        output.write(bytes([Instruction.ModusPonens]))

    def conclusion(self) -> Pattern:
        right_conclusion = self.right.conclusion()
        assert isinstance(right_conclusion, Implication)
        assert right_conclusion.left == self.left.conclusion(), (right_conclusion.left, self.left.conclusion())
        return right_conclusion.right


def modus_ponens(left: Proof, right: Proof) -> Proof:
    return ModusPonens(left, right)


@dataclass(frozen=True)
class Prop1(Proof):
    def serialize_impl(self, to_reuse: set[Term], memory: list[Term], output: BinaryIO) -> None:
        output.write(bytes([Instruction.Prop1]))

    def conclusion(self) -> Pattern:
        phi0: MetaVar = MetaVar(0)
        phi1: MetaVar = MetaVar(1)
        return implies(phi0, implies(phi1, phi0))


prop1 = Prop1()


@dataclass(frozen=True)
class Prop2(Proof):
    def serialize_impl(self, to_reuse: set[Term], memory: list[Term], output: BinaryIO) -> None:
        output.write(bytes([Instruction.Prop2]))

    def conclusion(self) -> Pattern:
        phi0: MetaVar = MetaVar(0)
        phi1: MetaVar = MetaVar(1)
        phi2: MetaVar = MetaVar(2)
        return implies(implies(phi0, implies(phi1, phi2)), implies(implies(phi0, phi1), implies(phi0, phi2)))


prop2 = Prop2()
