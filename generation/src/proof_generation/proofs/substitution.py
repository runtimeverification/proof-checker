from __future__ import annotations

import sys
from typing import TYPE_CHECKING

from proof_generation.aml import EVar, Exists, Implies, MetaVar, Notation
from proof_generation.proof import ProofExp
from proof_generation.proofs.definedness import equals
from proof_generation.proofs.propositional import Propositional, neg, phi0, phi1, top

if TYPE_CHECKING:
    from proof_generation.proof import ProofThunk


def forall(var: int) -> Notation:
    return Notation(f'forall_{var}', 1, neg(Exists(var, neg(phi0))), f'(∀ x{var} . {{0}})')


func_subst_axiom = Implies(
    Exists(0, equals(MetaVar(0, e_fresh=(EVar(0),)), EVar(0))),
    Implies(forall(1)(phi1), phi1.apply_esubst(1, MetaVar(0, e_fresh=(EVar(0),)))),
)

HOLE = EVar(0)


class Substitution(ProofExp):
    def __init__(self) -> None:
        super().__init__(
            axioms=[func_subst_axiom],
            notations=[forall(0)],
            claims=[forall(0)(top())],
        )
        self.prop = self.import_module(Propositional())
        self.add_proof_expression(self.top_univgen())

    def universal_gen(self, phi: ProofThunk, var: EVar) -> ProofThunk:
        """
        phi
        --------------------------------------
        forall {var} . phi
        """
        # (exists {var} (neg phi)) -> bot == forall {var} phi
        return self.exists_generalization(
            # neg phi -> bot
            self.modus_ponens(
                # phi -> (neg phi -> bot)
                self.prop.dneg_intro(phi.conc),
                phi,
            ),
            var,
        )

    def top_univgen(self) -> ProofThunk:
        """forall x0 . T"""
        return self.universal_gen(self.prop.top_intro(), EVar(0))

    def functional_subst(self, func_p_pf: ProofThunk, q_pf: ProofThunk) -> ProofThunk:
        """
          exists x0 . p = x0       forall x1. q
        -----------------------------------------------
                         q[p/x1]
        """
        return self.modus_ponens(self.modus_ponens(self.load_axiom(func_subst_axiom), func_p_pf), q_pf)


if __name__ == '__main__':
    Substitution().main(sys.argv)
