from __future__ import annotations

import sys
from dataclasses import dataclass
from typing import TYPE_CHECKING

from proof_generation.pattern import App, MetaVar, Notation, Symbol
from proof_generation.proof import ProofExp
from proof_generation.proofs.propositional import And, Negation, Or

if TYPE_CHECKING:
    from proof_generation.pattern import Pattern
    from proof_generation.proof import ProvedExpression

phi0 = MetaVar(0)
phi1 = MetaVar(1)
phi2 = MetaVar(2)

# TODO: Make sure this is handled uniformly
inhabitant_symbol = Symbol('inhabitant')
kore_next_symbol = Symbol('kore_next')
kore_dv_symbol = Symbol('kore_dv')


@dataclass(frozen=True, eq=False)
class KoreTop(Notation):
    phi0: Pattern

    @classmethod
    def definition(cls) -> Pattern:
        return App(inhabitant_symbol, phi0)

    def __str__(self) -> str:
        return f'(k⊤ {self.phi0})'


@dataclass(frozen=True, eq=False)
class KoreNot(Notation):
    phi0: Pattern
    phi1: Pattern

    @classmethod
    def definition(cls) -> Pattern:
        return And(Negation(phi1), KoreTop(phi0))

    def __str__(self) -> str:
        return f'(k¬ {self.phi0})'


@dataclass(frozen=True, eq=False)
class KoreAnd(Notation):
    phi0: Pattern
    phi1: Pattern
    phi2: Pattern

    @classmethod
    def definition(cls) -> Pattern:
        return And(phi1, phi2)

    def __str__(self) -> str:
        return f'({str(self.phi0)}[{str(self.phi1)}] k⋀ {str(self.phi0)}[{str(self.phi2)}])'


@dataclass(frozen=True, eq=False)
class KoreOr(Notation):
    phi0: Pattern
    phi1: Pattern
    phi2: Pattern

    @classmethod
    def definition(cls) -> Pattern:
        return Or(phi1, phi2)

    def __str__(self) -> str:
        return f'({str(self.phi0)}[{str(self.phi1)}] k⋁ {str(self.phi0)}[{str(self.phi2)}])'


@dataclass(frozen=True, eq=False)
class KoreNext(Notation):
    phi0: Pattern
    phi1: Pattern

    @classmethod
    def definition(cls) -> Pattern:
        return App(kore_next_symbol, phi1)

    def __str__(self) -> str:
        return f'(♦ {str(self.phi1)})'


@dataclass(frozen=True, eq=False)
class KoreImplies(Notation):
    phi0: Pattern
    phi1: Pattern
    phi2: Pattern

    @classmethod
    def definition(cls) -> Pattern:
        return KoreOr(phi0, KoreNot(phi0, phi1), phi2)

    def __str__(self) -> str:
        return f'({str(self.phi0)}[{str(self.phi1)}] k-> {str(self.phi0)}[{str(self.phi2)}])'


@dataclass(frozen=True, eq=False)
class KoreApplies(Notation):
    sorts: tuple[Pattern, ...]  # For sorts
    phi0: Pattern  # For arguments

    @classmethod
    def definition(cls) -> Pattern:
        # TODO: We just drop the sort for now
        # In the Kore we can have an application of a symbol to none or several arguments. We chain them manually
        # in a single pattern and then save it to phi1. We can't guarantee that there are two or more args as in
        # the normal application.
        return phi0

    def __str__(self) -> str:
        return f'(kapp({str(self.sorts)}) ({str(self.phi0)})'


@dataclass(frozen=True, eq=False)
class KoreRewrites(Notation):
    phi0: Pattern
    phi1: Pattern
    phi2: Pattern

    @classmethod
    def definition(cls) -> Pattern:
        return KoreImplies(phi0, phi1, KoreNext(phi0, phi2))

    def __str__(self) -> str:
        return f'({str(self.phi0)}[{str(self.phi1)}] k=> {str(self.phi0)}[{str(self.phi2)}])'


@dataclass(frozen=True, eq=False)
class KoreDv(Notation):
    phi0: Pattern
    phi1: Pattern

    @classmethod
    def definition(cls) -> Pattern:
        return App(App(kore_dv_symbol, phi0), phi1)


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
