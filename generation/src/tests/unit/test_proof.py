from __future__ import annotations

from abc import abstractmethod
from dataclasses import dataclass
from io import BytesIO
from typing import BinaryIO

# from abc import abstractmethod
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
    def instantiate(self: Proof, var: MetaVar, plug: Pattern) -> Proof:
        return Instantiate(self, var, plug)


@dataclass(frozen=True)
class Instantiate(Proof):
    subproof: Proof
    var: MetaVar
    plug: Pattern

    def well_formed(self) -> bool:
        return True

    def serialize_impl(self, to_reuse: set[Term], memory: list[Term], output: BinaryIO) -> None:
        self.subproof.serialize(to_reuse, memory, output)
        self.plug.serialize(to_reuse, memory, output)
        output.write(bytes([Instruction.Instantiate, self.var.name]))


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


# ===========================


def test_serialize_phi_implies_phi() -> None:
    phi0 = MetaVar(0)
    phi_implies_phi = implies(phi0, phi0)

    out = BytesIO()
    phi_implies_phi.serialize({phi0}, [], out)
    # fmt: off
    assert bytes(out.getbuffer()) == bytes([
        Instruction.List, 0,
        Instruction.List, 0,
        Instruction.List, 0,
        Instruction.List, 0,
        Instruction.List, 0,
        Instruction.MetaVar, 0,
        Instruction.Save,
        Instruction.Load, 0,
        Instruction.Implication,
    ])
    # fmt: on


def test_prove_imp_implies_imp() -> None:
    phi0 = MetaVar(0)
    phi1 = MetaVar(1)
    phi2 = MetaVar(2)
    phi0_implies_phi0 = implies(phi0, phi0)
    imp_reflexivity = modus_ponens(
        prop1.instantiate(phi1, phi0),
        modus_ponens(
            prop1.instantiate(phi1, phi0_implies_phi0),
            prop2.instantiate(phi1, phi0_implies_phi0).instantiate(phi2, phi0),
        ),
    )
    out = BytesIO()
    imp_reflexivity.serialize({phi0, phi0_implies_phi0}, [], out)
    # fmt: off
    assert bytes(out.getbuffer()) == bytes([
        Instruction.Prop1,              # (p1: phi0 -> (phi1 -> phi0))

        Instruction.List, 0,
        Instruction.List, 0,
        Instruction.List, 0,
        Instruction.List, 0,
        Instruction.List, 0,
        Instruction.MetaVar, 0,         # Stack: p1 ; phi0
        Instruction.Save,               # phi0 save at 0

        Instruction.Instantiate, 1,     # Stack: (p2: phi0 -> (phi0 -> phi0))

        Instruction.Prop1,              # Stack: p2 ; p1
        Instruction.Load, 0,            # Stack: p2 ; p1 ; phi0
        Instruction.Load, 0,            # Stack: p2 ; p1 ; phi0 ; phi0
        Instruction.Implication,        # Stack: p2 ; p1 ; phi1; phi0 -> phi0
        Instruction.Save,               # phi0 -> phi0 save at 1

        Instruction.Instantiate, 1,     # Stack: p2 ; (p3: phi0 -> ((phi0 -> phi0) -> phi0))

        Instruction.Prop2,              # Stack: p2 ; p3; (p4: (phi0 -> (phi1 -> phi2)) -> ((phi0 -> phi1) -> (phi0 -> phi2))
        Instruction.Load, 1,
        Instruction.Instantiate, 1,     # Stack: p2 ; p3; (p4: (phi0 -> ((phi0 -> phi0) -> phi2)) -> (p2 -> (phi0 -> phi2))

        Instruction.Load, 0,
        Instruction.Instantiate, 2,     # Stack: p2 ; p3; (p4: p3 -> (p2 -> (phi0 -> phi0))

        Instruction.ModusPonens,        # Stack: p2 ; (p2 -> (phi0 -> phi0))
        Instruction.ModusPonens,        # Stack: phi0 -> phi0
    ])
    # fmt: on
