from __future__ import annotations

from io import BytesIO

from proof_generation.instruction import Instruction
from proof_generation.proof import EVar, MetaVar, app, exists, implies, modus_ponens, mu, prop1, prop2
from proof_generation.proofs.propositional import Propositional


def test_instantiate() -> None:
    phi0 = MetaVar(0)
    phi0_ef0 = MetaVar(0, e_fresh=(EVar(0),))
    phi1 = MetaVar(1)
    assert phi0.instantiate(0, phi0_ef0) == phi0_ef0
    assert phi0.instantiate(1, phi0_ef0) == phi0

    assert implies(phi0, phi0).instantiate(0, phi1) == implies(phi1, phi1)
    assert implies(phi0, phi1).instantiate(2, phi0_ef0) == implies(phi0, phi1)

    assert app(phi0, phi0).instantiate(0, phi1) == app(phi1, phi1)
    assert app(phi0, phi1).instantiate(2, phi0_ef0) == app(phi0, phi1)

    assert exists(0, phi0).instantiate(0, phi1) == exists(0, phi1)
    assert exists(0, phi0).instantiate(0, phi0_ef0) == exists(0, phi0_ef0)
    assert exists(0, phi1).instantiate(2, phi0_ef0) == exists(0, phi1)

    assert mu(0, phi0).instantiate(0, phi1) == mu(0, phi1)
    assert mu(0, phi0).instantiate(0, phi0_ef0) == mu(0, phi0_ef0)
    assert mu(0, phi1).instantiate(2, phi0_ef0) == mu(0, phi1)


def test_conclusion() -> None:
    phi0 = MetaVar(0)
    phi1 = MetaVar(1)
    phi2 = MetaVar(2)
    prop = Propositional()

    step1 = prop1.instantiate(1, phi0)
    assert step1.conclusion() == implies(phi0, implies(phi0, phi0))

    step2 = prop1.instantiate(1, prop.phi0_implies_phi0)
    assert step2.conclusion() == implies(phi0, implies(prop.phi0_implies_phi0, phi0))

    assert prop2.conclusion() == implies(
        implies(phi0, implies(phi1, phi2)), implies(implies(phi0, phi1), implies(phi0, phi2))
    )

    step3 = prop2.instantiate(1, prop.phi0_implies_phi0)
    assert step3.conclusion() == implies(
        implies(phi0, implies(prop.phi0_implies_phi0, phi2)),
        implies(implies(phi0, prop.phi0_implies_phi0), implies(phi0, phi2)),
    )

    step4 = step3.instantiate(2, phi0)
    assert step4.conclusion() == implies(
        implies(phi0, implies(prop.phi0_implies_phi0, phi0)),
        implies(implies(phi0, prop.phi0_implies_phi0), implies(phi0, phi0)),
    )

    step4 = modus_ponens(step2, step4)
    assert step4.conclusion() == implies(implies(phi0, prop.phi0_implies_phi0), implies(phi0, phi0))

    step5 = modus_ponens(step1, step4)
    assert step5.conclusion() == implies(phi0, phi0)


def test_serialize_phi_implies_phi() -> None:
    out = BytesIO()
    Propositional().phi0_implies_phi0.serialize({Propositional().phi0}, [], out)
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
    assert Propositional().imp_reflexivity().conclusion() == Propositional().phi0_implies_phi0
    Propositional().imp_reflexivity().serialize({Propositional().phi0, Propositional().phi0_implies_phi0}, [], out)
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
        Instruction.Instantiate, 2,     # Stack: p2 ; p3; (p4: p3 -> (p2 -> (phi0 -> phi0)))

        Instruction.ModusPonens,        # Stack: p2 ; (p2 -> (phi0 -> phi0))
        Instruction.ModusPonens,        # Stack: phi0 -> phi0
    ])
    # fmt: on
