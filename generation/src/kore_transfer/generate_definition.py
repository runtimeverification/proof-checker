from __future__ import annotations

from collections.abc import Callable
from typing import TYPE_CHECKING

import proof_generation.proof as proof
from kore_transfer.language_semantics import KRewritingRule

if TYPE_CHECKING:
    from kore_transfer.generate_hints import KoreHint
    from kore_transfer.language_semantics import LanguageSemantics
    from proof_generation.pattern import Pattern

ProofMethod = Callable[[proof.ProofExp], proof.ProofThunk]


class KoreDefinition(proof.ProofExp):
    def __init__(self) -> None:
        super().__init__()

    def add_axioms(self, hint: KoreHint, language_semantics: LanguageSemantics) -> KRewritingRule:
        """Add axioms to the definition."""
        # TODO: We don't use them until the substitutions are implemented
        language_semantics.collect_functional_axioms(hint)
        assert isinstance(hint.axiom, KRewritingRule)
        self._axioms.append(hint.axiom.pattern)
        return hint.axiom

    def prove_rewrite_step(self, claim: Pattern, axiom: Pattern, instantiations: dict[int, Pattern]) -> None:
        """Take a single rewrite step and emit a proof for it."""
        assert len(self._axioms) > 0, 'No axioms to prove the rewrite step'
        self._claims.append(claim)
        self._proof_expressions.append(self.dynamic_inst(self.load_axiom(axiom), instantiations))
