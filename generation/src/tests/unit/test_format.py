from __future__ import annotations

from typing import TYPE_CHECKING

import pytest

from proof_generation.format import MLPrinter
from proof_generation.proof import EVar, Exists, MetaVar, Mu, SVar, bot, implies, neg
from proof_generation.proofs.propositional import Propositional

if TYPE_CHECKING:
    from pprint import PrettyPrinter

    from proof_generation.proof import Proof

mlp = MLPrinter()
mlpd = MLPrinter(desugar_axioms=True)


not_phi0 = neg(MetaVar(0))
some_diverse_pattern = Mu(SVar(0), Exists(EVar(0), implies(MetaVar(25, e_fresh=(EVar(5),)), bot)))
imp_refl = Propositional().imp_reflexivity()


@pytest.mark.parametrize(
    'formatter, input_, expected',
    # fmt: off
    [
        ( mlp, not_phi0, '¬φ0' ),
        ( mlp, some_diverse_pattern,
          'μ(SVar(0),\n'
          '  ∃(EVar(0),\n'
          '     ¬φ25(e_f=(EVar(5),))))'),
        ( mlp,
          imp_refl,
          'MP(Inst(Prop1(),\n'
          '         1,\n'
          '         φ0),\n'
          '   MP(Inst(Prop1(),\n'
          '             1,\n'
          '             Imp(φ0,\n'
          '                  φ0)),\n'
          '       Inst(Inst(Prop2(),\n'
          '                   1,\n'
          '                   Imp(φ0,\n'
          '                        φ0)),\n'
          '             2,\n'
          '             φ0)))',
        ),
        (
          mlpd,
          imp_refl,
          'MP(Inst(Imp(φ0,\n'
          '              Imp(φ1,\n'
          '                   φ0)),\n'
          '         1,\n'
          '         φ0),\n'
          '   MP(Inst(Imp(φ0,\n'
          '                  Imp(φ1,\n'
          '                       φ0)),\n'
          '             1,\n'
          '             Imp(φ0,\n'
          '                  φ0)),\n'
          '       Inst(Inst(Imp(Imp(φ0,\n'
          '                             Imp(φ1,\n'
          '                                  φ2)),\n'
          '                        Imp(Imp(φ0,\n'
          '                                  φ1),\n'
          '                             Imp(φ0,\n'
          '                                  φ2))),\n'
          '                   1,\n'
          '                   Imp(φ0,\n'
          '                        φ0)),\n'
          '             2,\n'
          '             φ0)))',
        ),
    ],
    # fmt: on
)
def test_pformat(formatter: PrettyPrinter, input_: Proof, expected: str) -> None:
    assert formatter.pformat(input_) == expected
