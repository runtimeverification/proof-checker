from __future__ import annotations

from abc import abstractmethod
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

    @abstractmethod
    def serialize_impl(self, to_reuse: set[Term], memory: list[Term], output: BinaryIO) -> None:
        raise NotImplementedError


class Pattern(Term):
    ...


@dataclass(frozen=True)
class EVar(Pattern):
    name: int

    def serialize_impl(self, to_reuse: set[Term], memory: list[Term], output: BinaryIO) -> None:
        raise NotImplementedError


@dataclass(frozen=True)
class SVar(Pattern):
    name: int

    def serialize_impl(self, to_reuse: set[Term], memory: list[Term], output: BinaryIO) -> None:
        raise NotImplementedError


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


@dataclass(frozen=True)
class Application(Pattern):
    left: Pattern
    right: Pattern

    def serialize_impl(self, to_reuse: set[Term], memory: list[Term], output: BinaryIO) -> None:
        raise NotImplementedError


@dataclass(frozen=True)
class Exists(Pattern):
    var: EVar
    subpattern: Pattern


@dataclass(frozen=True)
class Mu(Pattern):
    var: SVar
    subpattern: Pattern

    def serialize_impl(self, to_reuse: set[Term], memory: list[Term], output: BinaryIO) -> None:
        raise NotImplementedError


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


X = SVar(0)
bot = Mu(X, X)


def neg(p: Pattern) -> Pattern:
    return implies(p, bot)


def app(left: Pattern, right: Pattern) -> Pattern:
    return Application(left, right)


# Proofs
# ======


@dataclass(frozen=True)
class Proof(Term):
    def instantiate(self: Proof, var: int, plug: Pattern) -> Proof:
        return Instantiate(self, var, plug)


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


@dataclass(frozen=True)
class ModusPonens(Proof):
    left: Proof
    right: Proof
    ...

    def serialize_impl(self, to_reuse: set[Term], memory: list[Term], output: BinaryIO) -> None:
        self.left.serialize(to_reuse, memory, output)
        self.right.serialize(to_reuse, memory, output)
        output.write(bytes([Instruction.ModusPonens]))


def modus_ponens(left: Proof, right: Proof) -> Proof:
    return ModusPonens(left, right)


@dataclass(frozen=True)
class Prop1(Proof):
    def serialize_impl(self, to_reuse: set[Term], memory: list[Term], output: BinaryIO) -> None:
        output.write(bytes([Instruction.Prop1]))


prop1 = Prop1()


@dataclass(frozen=True)
class Prop2(Proof):
    def serialize_impl(self, to_reuse: set[Term], memory: list[Term], output: BinaryIO) -> None:
        output.write(bytes([Instruction.Prop2]))


prop2 = Prop2()
