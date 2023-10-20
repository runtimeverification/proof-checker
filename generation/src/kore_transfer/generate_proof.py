from __future__ import annotations

from typing import TYPE_CHECKING

import proof_generation.pattern as nf
import proof_generation.proofs.kore_lemmas as kl

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
        axiom = proof_expression.add_axiom(hint.axiom_ordinal, kore_converter)
        sort, _left, _right = kl.kore_rewrites.assert_matches(
            axiom, f'The hint should contain a rewriting rule, got {str(axiom)}'
        )
        claim = kl.kore_rewrites(sort, hint.configuration_before, hint.configuration_after)

        assert isinstance(axiom, nf.Pattern), f'The hint should contain a pattern, got {axiom}'
        proof_expression.prove_rewrite_step(claim, axiom, hint.instantiations)
        claims += 1

    print(f'Generated {claims} claims')
