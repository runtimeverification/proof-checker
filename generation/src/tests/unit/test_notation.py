from __future__ import annotations

from typing import TYPE_CHECKING

import pytest

from proof_generation.pattern import bot, imp
from proof_generation.proofs.propositional import Or, neg, phi0, phi1, phi2

if TYPE_CHECKING:
    from proof_generation.pattern import Pattern

test_pattern_pairs = [
    (phi0, phi0, True),
    (imp(phi0, phi1), imp(phi0, phi1), True),
    (imp(phi1, phi1), imp(phi0, phi1), False),
    (Or(phi0, phi1), imp(neg(phi0), phi1), True),
    (imp(neg(phi0), phi1), Or(phi0, phi1), True),
    (imp(neg(phi1), Or(phi2, phi0)), imp(neg(phi1), imp(imp(phi2, bot), phi0)), True),
    (imp(neg(phi1), imp(imp(phi2, bot), phi0)), imp(neg(phi1), Or(phi2, phi0)), True),
    (Or(Or(phi0, phi1), imp(phi1, Or(phi2, phi0))), Or(Or(phi0, phi1), imp(phi1, Or(phi2, phi0))), True),
    (Or(Or(phi0, phi1), imp(neg(phi1), Or(phi2, phi0))), Or(imp(neg(phi0), phi1), Or(phi1, Or(phi2, phi0))), True),
    (Or(Or(phi0, phi1), imp(neg(phi1), Or(phi2, phi0))), Or(imp(phi0, phi1), Or(phi1, Or(phi2, phi0))), False),
]


@pytest.mark.parametrize('pat_pair', test_pattern_pairs)
def test_eq(pat_pair: tuple[Pattern, Pattern, bool]) -> None:
    if pat_pair[2]:
        assert pat_pair[0] == pat_pair[1], f'{str(p)}\n!=\n{str(q)}\n'
    else:
        assert not (pat_pair[0] == pat_pair[1]), f'{str(p)}\n==\n{str(q)}\n'
