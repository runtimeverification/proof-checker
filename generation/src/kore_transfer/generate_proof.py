from __future__ import annotations

from typing import TYPE_CHECKING

import proof_generation.proofs.kore_lemmas as kl
from kore_transfer.language_semantics import KRewritingRule

if TYPE_CHECKING:
    from collections.abc import Iterator

    from kore_transfer.generate_definition import KoreDefinition
    from kore_transfer.generate_hints import KoreHint
    from kore_transfer.language_semantics import LanguageSemantics


def generate_proofs(
    hints: Iterator[KoreHint], proof_expression: type[KoreDefinition], language_semantics: LanguageSemantics
) -> None:
    claims = 0
    for hint in hints:
        axiom = proof_expression.add_axioms(hint, language_semantics)
        assert isinstance(axiom, KRewritingRule)
        rewrite_axiom = axiom.pattern
        sort, left, right = kl.kore_rewrites.assert_matches(rewrite_axiom)
        claim = kl.kore_rewrites(sort, hint.configuration_before, hint.configuration_after)

        proof_expression.prove_rewrite_step(claim, rewrite_axiom, hint.substitutions)
        claims += 1

    print(f'Generated {claims} claims')
