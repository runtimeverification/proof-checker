from __future__ import annotations

from ..pattern import MetaVar, Mu, Notation, Symbol, _or
from ..proofs.kore import nary_app

ml_eps = Notation('epsilon', 0, Symbol('eps'), 'epsilon')
ml_a = Notation('a', 0, Symbol('a'), 'a')
ml_b = Notation('b', 0, Symbol('b'), 'b')
ml_concat = nary_app(Symbol('concat'), 2, '[{0} {1}]')


def ml_accepting_node(node_id: int) -> Notation:
    return Notation(
        'accepting',
        2,
        Mu(node_id, _or(ml_eps(), _or(ml_concat(ml_a(), MetaVar(0)), ml_concat(ml_b(), MetaVar(1))))),
        f'accepting({node_id}, {{0}}, {{1}})',
    )
