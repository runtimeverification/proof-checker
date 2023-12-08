from __future__ import annotations

from typing import TYPE_CHECKING

import pytest

from proof_generation.proofs.propositional import Implies, bot, neg, phi0, phi1, top

if TYPE_CHECKING:
    from proof_generation.pattern import Pattern

# fmt: off
test_data = [
    ('Top',                   top(),                                    '⊤'),
    ('Bot_elim',              Implies(bot(), phi0),                     '(⊥ -> phi0)'),
    ('Double Negation elim',  Implies(neg(neg(phi0)), phi0),            '(¬¬phi0 -> phi0)'),
    ('Double Negation intro', Implies(phi0, neg(neg(phi0))),            '(phi0 -> ¬¬phi0)'),
    ('Absurd',                Implies(neg(phi0), Implies(phi0, phi1)),  '(¬phi0 -> (phi0 -> phi1))'),
    ('Peirce_bot',            Implies(Implies(neg(phi0), phi0), phi0),  '((¬phi0 -> phi0) -> phi0)'),
]
# fmt: on


@pytest.mark.parametrize('name,pattern,expected', test_data, ids=(x[0] for x in test_data))
def test_pretty_print_propositional(name: str, pattern: Pattern, expected: str) -> None:
    assert str(pattern) == expected
