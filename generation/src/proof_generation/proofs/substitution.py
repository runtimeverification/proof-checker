from __future__ import annotations

import sys
from typing import TYPE_CHECKING

from proof_generation.pattern import EVar, Exists, Implies, MetaVar, Notation
from proof_generation.proof import ProofExp
from proof_generation.proofs.definedness import equals
from proof_generation.proofs.propositional import Propositional, neg, phi0, phi1, top

if TYPE_CHECKING:
    from proof_generation.pattern import Pattern
    from proof_generation.proof import ProofThunk


def forall(var: int) -> Notation:
    return Notation(f'forall_{var}', 1, neg(Exists(var, neg(phi0))), f'(∀ x{var} . {{0}})')


def func_subst_axiom(forall_evar_name: int) -> Pattern:
    return Implies(
        Exists(0, equals(MetaVar(0, e_fresh=(EVar(0),)), EVar(0))),
        Implies(forall(forall_evar_name)(phi1), phi1.apply_esubst(forall_evar_name, MetaVar(0, e_fresh=(EVar(0),)))),
    )


class Substitution(ProofExp):
    def __init__(self) -> None:
        super().__init__(
            axioms=[],
            notations=[forall(0)],
            claims=[forall(0)(top())],
        )
        self.prop = Propositional()
        self.add_proof_expression(self.top_univgen())
        self._notations.extend(self.prop.get_notations())

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

    def functional_subst(self, func_p_pf: ProofThunk, q_pf: ProofThunk, univ_evar: EVar) -> ProofThunk:
        """
          exists x0 . p = x0       forall univ_evar. q
        -----------------------------------------------
                         q[p/univ_evar]
        """
        # TODO: Fix this by proving the alpha equivalent version of the axiom
        func_subst_axiom_instance = func_subst_axiom(univ_evar.name)
        return self.modus_ponens(
            self.prop.imp_match_l(
                self.modus_ponens(
                    self.prop.imp_match_l(self.load_axiom(func_subst_axiom_instance), func_p_pf.conc), func_p_pf
                ),
                q_pf.conc,
            ),
            q_pf,
        )


if __name__ == '__main__':
    Substitution().main(sys.argv)
