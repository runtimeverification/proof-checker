from __future__ import annotations

from typing import TYPE_CHECKING

import proof_generation.pattern as nf

if TYPE_CHECKING:
    from collections.abc import Iterator

    from kore_transfer.generate_definition import KoreDefinition
    from kore_transfer.generate_hints import KoreHint


def generate_proofs(hints: Iterator[KoreHint], proof_expression: type[KoreDefinition]) -> None:
    curr_hint: KoreHint = next(hints)
    for next_hint in hints:
        # TODO: Process as `KoreRewrite` instead
        claim = nf.Implies(curr_hint.pattern, next_hint.pattern)

        axiom = curr_hint.relevant_axiom
        proof_expression.prove_rewrite_step(claim, axiom, curr_hint.instantiations)
        curr_hint = next_hint
