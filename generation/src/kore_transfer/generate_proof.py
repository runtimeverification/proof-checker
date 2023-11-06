from __future__ import annotations

from typing import TYPE_CHECKING

import proof_generation.proofs.kore_lemmas as kl
from kore_transfer.kore_converter import AxiomType

if TYPE_CHECKING:
    from collections.abc import Iterator

    from kore_transfer.generate_definition import KoreDefinition
    from kore_transfer.generate_hints import KoreHint
    from kore_transfer.kore_converter import KoreConverter


def generate_proofs(
    hints: Iterator[KoreHint], proof_expression: type[KoreDefinition], kore_converter: KoreConverter
) -> None:
    claims = 0
    for hint in hints:
        axioms = proof_expression.add_axioms(hint, kore_converter)

        rewrite_axiom = axioms[AxiomType.RewriteRule][0].pattern
        assert isinstance(rewrite_axiom, kl.KoreRewrites), f'The hint should contain a pattern, got {rewrite_axiom}'
        claim = kl.KoreRewrites(rewrite_axiom.phi0, hint.configuration_before, hint.configuration_after)

        proof_expression.prove_rewrite_step(claim, rewrite_axiom, hint.substitutions)
        claims += 1

    print(f'Generated {claims} claims')
