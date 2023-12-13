from __future__ import annotations

from typing import TYPE_CHECKING

from ..pattern import MetaVar, Mu, Notation, Symbol, _or
from ..proofs.kore import nary_app
from ..proofs.propositional import Propositional

from typing import NamedTuple


class Words(Propositional):
    def __init__(self):
        super().__init__()
        self.add_notations([self.notations.eps, self.notations.a, self.notations.b, self.notations.concat])
        ten_nodes = (self.notations.accepting_node(i) for i in range(0, 10))
        self.add_notations(ten_nodes)

    class _Notations(NamedTuple):
        eps: Final = Notation('epsilon', 0, Symbol('eps'), 'epsilon')
        a: Final = Notation('a', 0, Symbol('a'), 'a')
        b: Final = Notation('b', 0, Symbol('b'), 'b')
        concat: Final = nary_app(Symbol('concat'), 2, '[{0} {1}]')

        def accepting_node(self, node_id: int) -> Notation:
            """Represents an accpeting node in a DFA"""
            return Notation(
                'accepting',
                2,
                Mu(node_id, _or(self.eps(), _or(self.concat(self.a(), MetaVar(0)), self.concat(self.b(), MetaVar(1))))),
                f'accepting({node_id}, {{0}}, {{1}})',
            )

    notations = _Notations()
