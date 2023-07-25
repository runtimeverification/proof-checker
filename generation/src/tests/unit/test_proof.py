from __future__ import annotations

from dataclasses import dataclass


class Term:
    ...


class Pattern(Term):
    ...


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


@dataclass(frozen=True)
class Application(Pattern):
    left: Pattern
    right: Pattern


@dataclass(frozen=True)
class Exists(Pattern):
    var: EVar
    subpattern: Pattern


@dataclass(frozen=True)
class Mu(Pattern):
    var: SVar
    subpattern: Pattern


@dataclass(frozen=True)
class MetaVar(Pattern):
    name: int
    e_fresh: tuple[EVar, ...] = ()
    s_fresh: tuple[SVar, ...] = ()
    positive: tuple[SVar, ...] = ()
    negative: tuple[SVar, ...] = ()
    application_context: tuple[EVar, ...] = ()


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


@dataclass
class Proof(Term):
    def instantiate(self, var: MetaVar, plug: Pattern) -> Proof:
        return InstantiateSchema(self, var, plug)


@dataclass
class InstantiateSchema(Proof):
    subproof: Proof
    var: MetaVar
    plug: Pattern

    def well_formed(self) -> bool:
        return True


@dataclass
class ModusPonens(Proof):
    left: Proof
    right: Proof
    ...


def modus_ponens(left: Proof, right: Proof) -> Proof:
    return ModusPonens(left, right)


@dataclass
class Prop1(Proof):
    ...


prop1 = Prop1()


@dataclass
class Prop2(Proof):
    ...


prop2 = Prop2()


# ===========================


def test_prove_imp_implies_imp() -> None:
    phi0 = MetaVar(0)
    phi1 = MetaVar(1)
    imp_reflexivity = modus_ponens(
        modus_ponens(prop1.instantiate(phi1, phi0), prop2.instantiate(phi1, implies(phi0, phi0))), prop1
    )
    assert imp_reflexivity.serialize() == b''
