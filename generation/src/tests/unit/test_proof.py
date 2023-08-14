from __future__ import annotations

from io import BytesIO

from proof_generation.instruction import Instruction
from proof_generation.proof import Application, EVar, Exists, Implication, MetaVar, ModusPonens, Mu, Prop1, Prop2, SVar
from proof_generation.proofs.propositional import Propositional


def test_instantiate() -> None:
    phi0 = MetaVar(0)
    phi0_ef0 = MetaVar(0, e_fresh=(EVar(0),))
    phi1 = MetaVar(1)
    assert phi0.instantiate((0,), (phi0_ef0,)) == phi0_ef0
    assert phi0.instantiate((1,), (phi0_ef0,)) == phi0

    assert Implication(phi0, phi0).instantiate((0,), (phi1,)) == Implication(phi1, phi1)
    assert Implication(phi0, phi1).instantiate((2,), (phi0_ef0,)) == Implication(phi0, phi1)

    assert Application(phi0, phi0).instantiate((0,), (phi1,)) == Application(phi1, phi1)
    assert Application(phi0, phi1).instantiate((2,), (phi0_ef0,)) == Application(phi0, phi1)

    assert Exists(EVar(0), phi0).instantiate((0,), (phi1,)) == Exists(EVar(0), phi1)
    assert Exists(EVar(0), phi0).instantiate((0,), (phi0_ef0,)) == Exists(EVar(0), phi0_ef0)
    assert Exists(EVar(0), phi1).instantiate((1,), (phi0_ef0,)) == Exists(EVar(0), phi0_ef0)
    assert Exists(EVar(0), phi1).instantiate((2,), (phi0_ef0,)) == Exists(EVar(0), phi1)

    assert Mu(SVar(0), phi0).instantiate((0,), (phi1,)) == Mu(SVar(0), phi1)
    assert Mu(SVar(0), phi0).instantiate((0,), (phi0_ef0,)) == Mu(SVar(0), phi0_ef0)
    assert Mu(SVar(0), phi1).instantiate((1,), (phi0_ef0,)) == Mu(SVar(0), phi0_ef0)
    assert Mu(SVar(0), phi1).instantiate((2,), (phi0_ef0,)) == Mu(SVar(0), phi1)


def test_conclusion() -> None:
    phi0 = MetaVar(0)
    phi1 = MetaVar(1)
    phi2 = MetaVar(2)
    prop = Propositional()

    step1 = Prop1().instantiate((1,), (phi0,))
    assert step1.conclusion() == Implication(phi0, Implication(phi0, phi0))

    step2 = Prop1().instantiate((1,), (prop.phi0_implies_phi0(),))
    assert step2.conclusion() == Implication(phi0, Implication(prop.phi0_implies_phi0(), phi0))

    assert Prop2().conclusion() == Implication(
        Implication(phi0, Implication(phi1, phi2)), Implication(Implication(phi0, phi1), Implication(phi0, phi2))
    )

    step3 = Prop2().instantiate((1,), (prop.phi0_implies_phi0(),))
    assert step3.conclusion() == Implication(
        Implication(phi0, Implication(prop.phi0_implies_phi0(), phi2)),
        Implication(Implication(phi0, prop.phi0_implies_phi0()), Implication(phi0, phi2)),
    )

    step4 = step3.instantiate((2,), (phi0,))
    assert step4.conclusion() == Implication(
        Implication(phi0, Implication(prop.phi0_implies_phi0(), phi0)),
        Implication(Implication(phi0, prop.phi0_implies_phi0()), Implication(phi0, phi0)),
    )

    step4 = ModusPonens(step4, step2)
    assert step4.conclusion() == Implication(Implication(phi0, prop.phi0_implies_phi0()), Implication(phi0, phi0))

    step5 = ModusPonens(step4, step1)
    assert step5.conclusion() == Implication(phi0, phi0)


def test_serialize_phi_implies_phi() -> None:
    out = BytesIO()
    Propositional().phi0_implies_phi0().serialize({Propositional().phi0()}, set(), [], [], out)
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
        Instruction.Implication,        # Stack: phi0 -> phi0
    ])
    # fmt: on


def test_prove_imp_reflexivity() -> None:
    prop = Propositional()
    out = BytesIO()
    assert prop.imp_reflexivity().conclusion() == prop.phi0_implies_phi0()
    prop.imp_reflexivity().serialize(
        {prop.phi0(), prop.phi0_implies_phi0()}, set(), [], [prop.phi0_implies_phi0()], out
    )
    # fmt: off
    assert bytes(out.getbuffer()) == bytes([
        Instruction.Prop2,              # Stack: prop2

        Instruction.List, 0,
        Instruction.List, 0,
        Instruction.List, 0,
        Instruction.List, 0,
        Instruction.List, 0,
        Instruction.MetaVar, 0,         # Stack: prop2 ; $ph0
        Instruction.Save,               # @0
        Instruction.Load, 0,            # Stack: prop2 ; $ph0 ; $ph0
        Instruction.Load, 0,            # Stack: prop2[ph0 -> ph0/0] ; ph0
        Instruction.Implication,        # Stack: prop2 ; $ph0 -> ph0
        Instruction.Save,               # @1
        Instruction.Instantiate, 2, 1, 2, # Stack: prop2[ph0 -> ph0/0]

        Instruction.Prop1,              # Stack: p1 ; prop1
        Instruction.Load, 1,            # Stack: p1 ; prop1 ; $ph0 -> ph0
        Instruction.Instantiate, 1, 1,  # Stack: p1 ; [p2: (ph0 -> (ph0 -> ph0) -> ph0) ]
        Instruction.ModusPonens,        # Stack: [p3: (ph0 -> (ph0 -> ph0)) -> (ph0 -> ph0)]

        Instruction.Prop1,              # Stack: p3 ; prop1
        Instruction.Load, 0,            # Stack: p3 ; prop1 ; ph0
        Instruction.Instantiate, 1, 1,  # Stack: p3 ; ph0 -> ph0 -> ph0

        Instruction.ModusPonens,        # Stack: phi0 -> phi0
        Instruction.Publish,
    ])
    # fmt: on
