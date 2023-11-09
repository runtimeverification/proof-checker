from __future__ import annotations

from typing import TYPE_CHECKING

import proof_generation.proofs.kore_lemmas as kl
from kore_transfer.kore_converter import KRewritingRule

if TYPE_CHECKING:
    from collections.abc import Iterator

    from kore_transfer.generate_definition import KoreDefinition
    from kore_transfer.generate_hints import KoreHint
    from kore_transfer.kore_converter import LanguageSemantics


def generate_proofs(
    hints: Iterator[KoreHint], proof_expression: type[KoreDefinition], kore_converter: LanguageSemantics
) -> None:
    claims = 0
    for hint in hints:
        axiom = proof_expression.add_axioms(hint, kore_converter)
        assert isinstance(axiom, KRewritingRule)

        rewrite_axiom = axiom.pattern
        assert isinstance(rewrite_axiom, kl.KoreRewrites), f'The hint should contain a pattern, got {rewrite_axiom}'
        claim = kl.KoreRewrites(rewrite_axiom.phi0, hint.configuration_before, hint.configuration_after)

        proof_expression.prove_rewrite_step(claim, rewrite_axiom, hint.substitutions)
        claims += 1

    print(f'Generated {claims} claims')
