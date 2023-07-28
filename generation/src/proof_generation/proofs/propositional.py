from __future__ import annotations

import sys
from typing import TYPE_CHECKING

from proof_generation.proof import MetaVar, implies, modus_ponens, prop1, prop2

if TYPE_CHECKING:
    from proof_generation.proof import Pattern, Proof


class Propositional:
    def theory(self) -> list[Pattern]:
        """Returns a list of axioms. In this case we do not rely on any axioms."""
        return []

    def lemmas(self) -> set[Pattern]:
        """Returns a list statements for lemmas that we should reuse."""
        return set()

    def notation(self) -> set[Pattern]:
        """Returns a list patterns that we will want to reuse."""
        return {self.phi0}

    def published(self) -> set[Pattern]:
        """Returns a list statements for theorems that we want to publish."""
        return {self.phi0_implies_phi0}

    def proof(self) -> list[Proof]:
        """Returns a list of proofs for the published statements."""
        return [self.imp_reflexivity]

    phi0: MetaVar = MetaVar(0)

    phi0_implies_phi0: Pattern = implies(phi0, phi0)
    imp_reflexivity: Proof = modus_ponens(
        prop1.instantiate(1, phi0),
        modus_ponens(
            prop1.instantiate(1, phi0_implies_phi0),
            prop2.instantiate(1, phi0_implies_phi0).instantiate(2, phi0),
        ),
    )


if __name__ == '__main__':
    _exe, proof_path = sys.argv
    with open(proof_path, 'wb') as out:
        Propositional.imp_reflexivity.serialize({Propositional.phi0, Propositional.phi0_implies_phi0}, [], out)
