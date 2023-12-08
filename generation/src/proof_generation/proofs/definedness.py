from __future__ import annotations

from proof_generation.pattern import App, EVar, Exists, Implies, MetaVar, Notation, Symbol
from proof_generation.proof import ProofExp
from proof_generation.proofs.propositional import equiv, neg, phi0, phi1

definedness_symbol = Symbol('⌈_⌉')

ceil = Notation('ceil', 1, App(definedness_symbol, phi0), '⌈ {0} ⌉')
floor = Notation('floor', 1, neg(ceil(neg(phi0))), '⌊ {0} ⌋')
subset = Notation('subset', 2, floor(Implies(phi0, phi1)), '({0} ⊆ {1})')
equals = Notation('equals', 2, floor(equiv(phi0, phi1)), '({0} = {1})')
functional = Notation('functional', 1, Exists(0, equals(EVar(0), MetaVar(0, (EVar(0),)))), 'functional({0})')


class Definedness(ProofExp):
    def __init__(self) -> None:
        super().__init__(
            axioms=[ceil(EVar(0))],
        )
