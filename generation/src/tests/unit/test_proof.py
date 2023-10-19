from __future__ import annotations

from io import BytesIO, StringIO
from typing import TYPE_CHECKING

import pytest

from proof_generation.basic_interpreter import ExecutionPhase
from proof_generation.claim import Claim
from proof_generation.deserialize import deserialize_instructions
from proof_generation.instruction import Instruction
from proof_generation.pattern import Application, EVar, Exists, Implication, MetaVar, Mu
from proof_generation.pretty_printing_interpreter import NotationlessPrettyPrinter, PrettyPrintingInterpreter
from proof_generation.proofs.propositional import Propositional
from proof_generation.serializing_interpreter import SerializingInterpreter
from proof_generation.stateful_interpreter import StatefulInterpreter

if TYPE_CHECKING:
    from proof_generation.proof import Pattern


def test_pop() -> None:
    interpreter = PrettyPrintingInterpreter(phase=ExecutionPhase.Proof, out=StringIO())
    push_and_pop = bytes([Instruction.Prop1, Instruction.Pop])
    deserialize_instructions(data=push_and_pop, interpreter=interpreter)
    assert len(interpreter.stack) == 0


def test_instantiate() -> None:
    phi0 = MetaVar(0)
    phi0_ef0 = MetaVar(0, e_fresh=(EVar(0),))
    phi1 = MetaVar(1)
    assert phi0.instantiate({0: phi0_ef0}) == phi0_ef0
    assert phi0.instantiate({1: phi0_ef0}) == phi0

    assert Implication(phi0, phi0).instantiate({0: phi1}) == Implication(phi1, phi1)
    assert Implication(phi0, phi1).instantiate({2: phi0_ef0}) == Implication(phi0, phi1)

    assert Application(phi0, phi0).instantiate({0: phi1}) == Application(phi1, phi1)
    assert Application(phi0, phi1).instantiate({2: phi0_ef0}) == Application(phi0, phi1)

    assert Exists(0, phi0).instantiate({0: phi1}) == Exists(0, phi1)
    assert Exists(0, phi0).instantiate({0: phi0_ef0}) == Exists(0, phi0_ef0)
    assert Exists(0, phi1).instantiate({1: phi0_ef0}) == Exists(0, phi0_ef0)
    assert Exists(0, phi1).instantiate({2: phi0_ef0}) == Exists(0, phi1)

    assert Mu(0, phi0).instantiate({0: phi1}) == Mu(0, phi1)
    assert Mu(0, phi0).instantiate({0: phi0_ef0}) == Mu(0, phi0_ef0)
    assert Mu(0, phi1).instantiate({1: phi0_ef0}) == Mu(0, phi0_ef0)
    assert Mu(0, phi1).instantiate({2: phi0_ef0}) == Mu(0, phi1)


def test_conclusion() -> None:
    phi0 = MetaVar(0)
    phi0_implies_phi0 = Implication(phi0, phi0)
    prop = Propositional(StatefulInterpreter(phase=ExecutionPhase.Proof))
    prop.modus_ponens(
        prop.modus_ponens(
            prop.dynamic_inst(prop.prop2, {1: phi0_implies_phi0, 2: phi0}).assertc(
                Implication(
                    Implication(phi0, Implication(phi0_implies_phi0, phi0)),
                    Implication(Implication(phi0, phi0_implies_phi0), Implication(phi0, phi0)),
                )
            ),
            prop.dynamic_inst(prop.prop1, {1: phi0_implies_phi0}).assertc(
                Implication(phi0, Implication(phi0_implies_phi0, phi0))
            ),
        ).assertc(Implication(Implication(phi0, phi0_implies_phi0), Implication(phi0, phi0))),
        prop.dynamic_inst(prop.prop1, {1: phi0}),
    ).assertc(Implication(phi0, phi0))


def uncons_metavar_instrs(id: int) -> list[int]:
    return [Instruction.CleanMetaVar, id]


def test_prove_imp_reflexivity() -> None:
    out = BytesIO()
    phi0 = MetaVar(0)
    phi0_implies_phi0 = Implication(phi0, phi0)
    prop = Propositional(SerializingInterpreter(phase=ExecutionPhase.Proof, claims=[Claim(phi0_implies_phi0)], out=out))
    proved = prop.publish_proof(prop.imp_reflexivity())
    assert proved.conclusion == phi0_implies_phi0
    # fmt: off
    assert bytes(out.getbuffer()) == bytes([
        *uncons_metavar_instrs(0),          # Stack: ph0
        *uncons_metavar_instrs(0),          # Stack: ph0, ph0
        Instruction.Implication,            # Stack: ph0 -> ph0
        *uncons_metavar_instrs(0),          # Stack: ph0 -> ph0; ph0
        Instruction.Prop2,                  # Stack: ph0 -> ph0; ph0; prop2
        Instruction.Instantiate, 2, 2, 1,   # Stack: p1=[(ph0 -> ((ph0 -> ph0) -> ph0)) -> ((ph0 -> (ph0 -> ph0)) -> (ph0 -> ph0))]
        *uncons_metavar_instrs(0),          # Stack: p1; ph0;
        *uncons_metavar_instrs(0),          # Stack: p1; ph0; ph0;
        Instruction.Implication,            # Stack: p1 ; ph0 -> ph0;
        Instruction.Prop1,                  # Stack: p1 ; ph0 -> ph0; prop1
        Instruction.Instantiate, 1, 1,      # Stack: p1 ; [p2: (ph0 -> ((ph0 -> ph0) -> ph0)) ]
        Instruction.ModusPonens,            # Stack: [p3: ((ph0 -> (ph0 -> ph0)) -> (ph0 -> ph0))
        *uncons_metavar_instrs(0),          # Stack: p3 ; ph0;
        Instruction.Prop1,                  # Stack: p3; ph0; prop1
        Instruction.Instantiate, 1, 1,      # Stack: p3; ph0 -> (ph0 -> ph0)
        Instruction.ModusPonens,            # Stack: phi0 -> phi0
        Instruction.Publish,
    ])
    # fmt: on


# Construct a mock ProofExp to extract the claim and proof names
mock_prop = Propositional(SerializingInterpreter(phase=ExecutionPhase.Proof, out=BytesIO()))

proofs = [(method.__name__, ExecutionPhase.Proof) for method in mock_prop.proof_expressions()]


@pytest.mark.parametrize('test', proofs)
def test_deserialize_proof(test: tuple[str, ExecutionPhase]) -> None:
    (target, phase) = test
    # Serialize the target and deserialize the resulting bytes with the PrettyPrintingInterpreter
    out_ser = BytesIO()
    interpreter_ser = SerializingInterpreter(phase=phase, out=out_ser)
    _ = Propositional(interpreter_ser).__getattribute__(target)()
    out_ser_deser = StringIO()
    interpreter_ser_deser = NotationlessPrettyPrinter(phase=phase, out=out_ser_deser)
    deserialize_instructions(out_ser.getvalue(), interpreter_ser_deser)

    # Prettyprint the proof directly, but omit notation
    out_pretty = StringIO()
    interpreter_pretty = NotationlessPrettyPrinter(phase=phase, out=out_pretty)
    _ = Propositional(interpreter_pretty).__getattribute__(target)()

    assert out_pretty.getvalue() == out_ser_deser.getvalue()


claims = [(claim, ExecutionPhase.Claim) for claim in mock_prop.claims()]


@pytest.mark.parametrize('test', claims)
def test_deserialize_claim(test: tuple[Pattern, ExecutionPhase]) -> None:
    (target, phase) = test
    # Serialize the target and deserialize the resulting bytes with the PrettyPrintingInterpreter
    out_ser = BytesIO()
    interpreter_ser = SerializingInterpreter(phase=phase, out=out_ser)
    _ = Propositional(interpreter_ser).interpreter.pattern(target)
    out_ser_deser = StringIO()
    interpreter_ser_deser = NotationlessPrettyPrinter(phase=phase, out=out_ser_deser)
    deserialize_instructions(out_ser.getvalue(), interpreter_ser_deser)

    # Prettyprint the claim directly, but omit notation
    out_pretty = StringIO()
    interpreter_pretty = NotationlessPrettyPrinter(phase=phase, out=out_pretty)
    _ = Propositional(interpreter_pretty).interpreter.pattern(target)

    assert out_pretty.getvalue() == out_ser_deser.getvalue()
