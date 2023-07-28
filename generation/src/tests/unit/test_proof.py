from __future__ import annotations

from io import BytesIO

from proof_generation.instruction import Instruction
from proof_generation.proofs.propositional import Propositional


def test_serialize_phi_implies_phi() -> None:
    out = BytesIO()
    Propositional.phi0_implies_phi0.serialize({Propositional.phi0}, [], out)
    # fmt: off
    assert bytes(out.getbuffer()) == bytes([
        Instruction.List, 0,
        Instruction.List, 0,
        Instruction.List, 0,
        Instruction.List, 0,
        Instruction.List, 0,
        Instruction.MetaVar, 0,
        Instruction.Save,
        Instruction.Load, 0,
        Instruction.Implication,
    ])
    # fmt: on


def test_prove_imp_implies_imp() -> None:
    out = BytesIO()
    Propositional.imp_reflexivity.serialize({Propositional.phi0, Propositional.phi0_implies_phi0}, [], out)
    # fmt: off
    assert bytes(out.getbuffer()) == bytes([
        Instruction.Prop1,              # (p1: phi0 -> (phi1 -> phi0))

        Instruction.List, 0,
        Instruction.List, 0,
        Instruction.List, 0,
        Instruction.List, 0,
        Instruction.List, 0,
        Instruction.MetaVar, 0,         # Stack: p1 ; phi0
        Instruction.Save,               # phi0 save at 0

        Instruction.Instantiate, 1,     # Stack: (p2: phi0 -> (phi0 -> phi0))

        Instruction.Prop1,              # Stack: p2 ; p1
        Instruction.Load, 0,            # Stack: p2 ; p1 ; phi0
        Instruction.Load, 0,            # Stack: p2 ; p1 ; phi0 ; phi0
        Instruction.Implication,        # Stack: p2 ; p1 ; phi1; phi0 -> phi0
        Instruction.Save,               # phi0 -> phi0 save at 1

        Instruction.Instantiate, 1,     # Stack: p2 ; (p3: phi0 -> ((phi0 -> phi0) -> phi0))

        Instruction.Prop2,              # Stack: p2 ; p3; (p4: (phi0 -> (phi1 -> phi2)) -> ((phi0 -> phi1) -> (phi0 -> phi2))
        Instruction.Load, 1,
        Instruction.Instantiate, 1,     # Stack: p2 ; p3; (p4: (phi0 -> ((phi0 -> phi0) -> phi2)) -> (p2 -> (phi0 -> phi2))

        Instruction.Load, 0,
        Instruction.Instantiate, 2,     # Stack: p2 ; p3; (p4: p3 -> (p2 -> (phi0 -> phi0))

        Instruction.ModusPonens,        # Stack: p2 ; (p2 -> (phi0 -> phi0))
        Instruction.ModusPonens,        # Stack: phi0 -> phi0
    ])
    # fmt: on
