from __future__ import annotations

from dataclasses import dataclass
from typing import BinaryIO

from proof_generation.instruction import Instruction


class Term:
    ...

    def serialize(
        self,
        notation: set[Pattern],
        lemmas: set[Pattern],
        memory: list[tuple[bool, Pattern]],
        claims: list[Pattern],
        output: BinaryIO,
    ) -> None:
        if isinstance(self, Pattern) and (False, self) in memory:
            output.write(bytes([Instruction.Load, memory.index((False, self))]))
            return
        if isinstance(self, Proof) and (True, self.conclusion()) in memory:
            output.write(bytes([Instruction.Load, memory.index((True, self.conclusion()))]))
            return

        self.serialize_impl(notation, lemmas, memory, claims, output)

        # TODO: Check if needed lemma is already on the top of the stack.
        if isinstance(self, Pattern) and self in notation:
            memory.append((False, self))
            output.write(bytes([Instruction.Save]))
        if isinstance(self, Proof) and self.conclusion() in lemmas:
            memory.append((True, self.conclusion()))
            output.write(bytes([Instruction.Save]))

        if isinstance(self, Proof) and self.conclusion() in claims:
            claims.remove(self.conclusion())
            output.write(bytes([Instruction.Publish]))

    def serialize_impl(
        self,
        notation: set[Pattern],
        lemmas: set[Pattern],
        memory: list[tuple[bool, Pattern]],
        claims: list[Pattern],
        output: BinaryIO,
    ) -> None:
        raise NotImplementedError


class Pattern(Term):
    def instantiate(self, var: int, plug: Pattern) -> Pattern:
        raise NotImplementedError


@dataclass(frozen=True)
class EVar(Pattern):
    name: int

    def instantiate(self, var: int, plug: Pattern) -> Pattern:
        return self

    def serialize_impl(
        self,
        notation: set[Pattern],
        lemmas: set[Pattern],
        memory: list[tuple[bool, Pattern]],
        claims: list[Pattern],
        output: BinaryIO,
    ) -> None:
        output.write(bytes([Instruction.EVar, self.name]))


@dataclass(frozen=True)
class SVar(Pattern):
    name: int

    def instantiate(self, var: int, plug: Pattern) -> Pattern:
        return self

    def serialize_impl(
        self,
        notation: set[Pattern],
        lemmas: set[Pattern],
        memory: list[tuple[bool, Pattern]],
        claims: list[Pattern],
        output: BinaryIO,
    ) -> None:
        output.write(bytes([Instruction.SVar, self.name]))


@dataclass(frozen=True)
class Symbol(Pattern):
    name: int

    def instantiate(self, var: int, plug: Pattern) -> Pattern:
        return self

    def serialize_impl(
        self,
        notation: set[Pattern],
        lemmas: set[Pattern],
        memory: list[tuple[bool, Pattern]],
        claims: list[Pattern],
        output: BinaryIO,
    ) -> None:
        output.write(bytes([Instruction.Symbol, self.name]))


@dataclass(frozen=True)
class Implication(Pattern):
    left: Pattern
    right: Pattern

    def serialize_impl(
        self,
        notation: set[Pattern],
        lemmas: set[Pattern],
        memory: list[tuple[bool, Pattern]],
        claims: list[Pattern],
        output: BinaryIO,
    ) -> None:
        self.left.serialize(notation, lemmas, memory, claims, output)
        self.right.serialize(notation, lemmas, memory, claims, output)
        output.write(bytes([Instruction.Implication]))

    def instantiate(self, var: int, plug: Pattern) -> Pattern:
        return Implication(self.left.instantiate(var, plug), self.right.instantiate(var, plug))


@dataclass(frozen=True)
class Application(Pattern):
    left: Pattern
    right: Pattern

    def serialize_impl(
        self,
        notation: set[Pattern],
        lemmas: set[Pattern],
        memory: list[tuple[bool, Pattern]],
        claims: list[Pattern],
        output: BinaryIO,
    ) -> None:
        self.left.serialize(notation, lemmas, memory, claims, output)
        self.right.serialize(notation, lemmas, memory, claims, output)
        output.write(bytes([Instruction.Application]))

    def instantiate(self, var: int, plug: Pattern) -> Pattern:
        return Application(self.left.instantiate(var, plug), self.right.instantiate(var, plug))


@dataclass(frozen=True)
class Exists(Pattern):
    var: EVar
    subpattern: Pattern

    def serialize_impl(
        self,
        notation: set[Pattern],
        lemmas: set[Pattern],
        memory: list[tuple[bool, Pattern]],
        claims: list[Pattern],
        output: BinaryIO,
    ) -> None:
        self.subpattern.serialize(notation, lemmas, memory, claims, output)
        output.write(bytes([Instruction.Exists, self.var.name]))

    def instantiate(self, var: int, plug: Pattern) -> Pattern:
        return Exists(self.var, self.subpattern.instantiate(var, plug))


@dataclass(frozen=True)
class Mu(Pattern):
    var: SVar
    subpattern: Pattern

    def serialize_impl(
        self,
        notation: set[Pattern],
        lemmas: set[Pattern],
        memory: list[tuple[bool, Pattern]],
        claims: list[Pattern],
        output: BinaryIO,
    ) -> None:
        self.subpattern.serialize(notation, lemmas, memory, claims, output)
        output.write(bytes([Instruction.Mu, self.var.name]))

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

    def serialize_impl(
        self,
        notation: set[Pattern],
        lemmas: set[Pattern],
        memory: list[tuple[bool, Pattern]],
        claims: list[Pattern],
        output: BinaryIO,
    ) -> None:
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


# Proofs
# ======


@dataclass(frozen=True)
class Proof(Term):
    def instantiate(self: Proof, var: int, plug: Pattern) -> Proof:
        return Instantiate(self, var, plug)

    def conclusion(self) -> Pattern:
        raise NotImplementedError

    def __post_init__(self) -> None:
        self.conclusion()


@dataclass(frozen=True)
class Instantiate(Proof):
    subproof: Proof
    var: int
    plug: Pattern

    def well_formed(self) -> bool:
        return True

    def serialize_impl(self, to_reuse: set[Term], memory: list[Term], claims: list[Pattern], output: BinaryIO) -> None:
        self.subproof.serialize(to_reuse, memory, claims, output)
        self.plug.serialize(to_reuse, memory, claims, output)
        output.write(bytes([Instruction.Instantiate, 1, self.var]))

    def conclusion(self) -> Pattern:
        return self.subproof.conclusion().instantiate(self.var, self.plug)


@dataclass(frozen=True)
class ModusPonens(Proof):
    left: Proof
    right: Proof
    ...

    def serialize_impl(
        self,
        notation: set[Pattern],
        lemmas: set[Pattern],
        memory: list[tuple[bool, Pattern]],
        claims: list[Pattern],
        output: BinaryIO,
    ) -> None:
        self.left.serialize(notation, lemmas, memory, claims, output)
        self.right.serialize(notation, lemmas, memory, claims, output)
        output.write(bytes([Instruction.ModusPonens]))

    def conclusion(self) -> Pattern:
        right_conclusion = self.right.conclusion()
        assert isinstance(right_conclusion, Implication)
        assert right_conclusion.left == self.left.conclusion(), (right_conclusion.left, self.left.conclusion())
        return right_conclusion.right


@dataclass(frozen=True)
class Prop1(Proof):
    def serialize_impl(
        self,
        notation: set[Pattern],
        lemmas: set[Pattern],
        memory: list[tuple[bool, Pattern]],
        claims: list[Pattern],
        output: BinaryIO,
    ) -> None:
        output.write(bytes([Instruction.Prop1]))

    def conclusion(self) -> Pattern:
        phi0: MetaVar = MetaVar(0)
        phi1: MetaVar = MetaVar(1)
        return implies(phi0, implies(phi1, phi0))


@dataclass(frozen=True)
class Prop2(Proof):
    def serialize_impl(
        self,
        notation: set[Pattern],
        lemmas: set[Pattern],
        memory: list[tuple[bool, Pattern]],
        claims: list[Pattern],
        output: BinaryIO,
    ) -> None:
        output.write(bytes([Instruction.Prop2]))

    def conclusion(self) -> Pattern:
        phi0: MetaVar = MetaVar(0)
        phi1: MetaVar = MetaVar(1)
        phi2: MetaVar = MetaVar(2)
        return implies(implies(phi0, implies(phi1, phi2)), implies(implies(phi0, phi1), implies(phi0, phi2)))
