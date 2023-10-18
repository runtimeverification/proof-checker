from __future__ import annotations

import sys
from dataclasses import dataclass
from typing import TYPE_CHECKING

from proof_generation.pattern import Application, MetaVar, Notation, Symbol
from proof_generation.proof import ProofExp
from proof_generation.proofs.propositional import And, Negation, Or

if TYPE_CHECKING:
    from proof_generation.pattern import Pattern
    from proof_generation.proof import ProvedExpression

phi0 = MetaVar(0)
phi1 = MetaVar(1)
phi2 = MetaVar(2)

# TODO: Make sure this is handled uniformly
inhabitant_symbol = Symbol(0)
kore_next_symbol = Symbol(1)
kore_dv_symbol = Symbol(2)


@dataclass(frozen=True, eq=False)
class KoreTop(Notation):
    phi0: Pattern

    @staticmethod
    def definition() -> Pattern:
        return Application(inhabitant_symbol, phi0)

    def __str__(self) -> str:
        return f'(k\u22A4 {self.phi0})'


@dataclass(frozen=True, eq=False)
class KoreNot(Notation):
    phi0: Pattern
    phi1: Pattern

    @staticmethod
    def definition() -> Pattern:
        return And(Negation(phi1), KoreTop(phi0))

    def __str__(self) -> str:
        return f'(k\u22A4 {self.phi0})'


@dataclass(frozen=True, eq=False)
class KoreAnd(Notation):
    phi0: Pattern
    phi1: Pattern
    phi2: Pattern

    @staticmethod
    def definition() -> Pattern:
        return And(phi1, phi2)

    def __str__(self) -> str:
        return f'({str(self.phi0)}[{str(self.phi1)}] k/\\ {str(self.phi0)}[{str(self.phi2)}])'


@dataclass(frozen=True, eq=False)
class KoreOr(Notation):
    phi0: Pattern
    phi1: Pattern
    phi2: Pattern

    @staticmethod
    def definition() -> Pattern:
        return Or(phi1, phi2)

    def __str__(self) -> str:
        return f'({str(self.phi0)}[{str(self.phi1)}] k\\/ {str(self.phi0)}[{str(self.phi2)}])'


@dataclass(frozen=True, eq=False)
class KoreNext(Notation):
    phi0: Pattern
    phi1: Pattern

    @staticmethod
    def definition() -> Pattern:
        return Application(kore_next_symbol, phi1)

    def __str__(self) -> str:
        return f'(\u2666 {str(self.phi1)})'


@dataclass(frozen=True, eq=False)
class KoreImplies(Notation):
    phi0: Pattern
    phi1: Pattern
    phi2: Pattern

    @staticmethod
    def definition() -> Pattern:
        return KoreOr(phi0, KoreNot(phi0, phi1), phi2)

    def __str__(self) -> str:
        return f'({str(self.phi0)}[{str(self.phi1)}] k-> {str(self.phi0)}[{str(self.phi2)}])'


@dataclass(frozen=True, eq=False)
class KoreRewrites(Notation):
    phi0: Pattern
    phi1: Pattern
    phi2: Pattern

    @staticmethod
    def definition() -> Pattern:
        return KoreImplies(phi0, phi1, KoreNext(phi0, phi2))

    def __str__(self) -> str:
        return f'({str(self.phi0)}[{str(self.phi1)}] k=> {str(self.phi0)}[{str(self.phi2)}])'


@dataclass(frozen=True, eq=False)
class KoreDv(Notation):
    phi0: Pattern
    phi1: Pattern

    @staticmethod
    def definition() -> Pattern:
        return Application(Application(kore_dv_symbol, phi0), phi1)


# TODO: Add kore-transitivity
class KoreLemmas(ProofExp):
    @staticmethod
    def axioms() -> list[Pattern]:
        return []

    @staticmethod
    def claims() -> list[Pattern]:
        return []

    def proof_expressions(self) -> list[ProvedExpression]:
        return []


if __name__ == '__main__':
    KoreLemmas.main(sys.argv)
