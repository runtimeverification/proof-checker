from __future__ import annotations

from io import BytesIO

from proof_generation.instruction import Instruction
from proof_generation.proof import (
    Application,
    Claim,
    EVar,
    Exists,
    Implication,
    MetaVar,
    Mu,
    SerializingInterpreter,
    StatefulInterpreter,
    SVar,
)
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
    phi0_implies_phi0 = Implication(phi0, phi0)
    prop = Propositional(StatefulInterpreter([]))
    prop.modus_ponens(
        prop.modus_ponens(
            prop.prop2()
            .instantiate((1, 2), (prop.phi0_implies_phi0(), prop.phi0()))
            .assertc(
                Implication(
                    Implication(phi0, Implication(phi0_implies_phi0, phi0)),
                    Implication(Implication(phi0, phi0_implies_phi0), Implication(phi0, phi0)),
                )
            ),
            prop.prop1()
            .instantiate((1,), (prop.phi0_implies_phi0(),))
            .assertc(Implication(phi0, Implication(phi0_implies_phi0, phi0))),
        ).assertc(Implication(Implication(phi0, phi0_implies_phi0), Implication(phi0, phi0))),
        prop.prop1().instantiate((1,), (prop.phi0(),)),
    ).assertc(Implication(phi0, phi0))


def test_serialize_phi_implies_phi() -> None:
    out = BytesIO()
    prop = Propositional(SerializingInterpreter(claims=[], out=out))
    prop.phi0_implies_phi0()
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
        Instruction.Save,
    ])
    # fmt: on


def test_prove_imp_reflexivity() -> None:
    out = BytesIO()
    phi0 = MetaVar(0)
    phi0_implies_phi0 = Implication(phi0, phi0)
    prop = Propositional(SerializingInterpreter(claims=[Claim(phi0_implies_phi0)], out=out))
    proved = prop.publish(prop.imp_reflexivity())
    assert proved.conclusion == phi0_implies_phi0
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
        Instruction.Implication,        # Stack: prop2 ; $ph0 -> ph0
        Instruction.Save,               # @1
        Instruction.Load, 0,            # Stack: prop2[ph0 -> ph0/0] ; ph0
        Instruction.Instantiate, 2, 2, 1, # Stack: prop2[ph0 -> ph0/0]

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
