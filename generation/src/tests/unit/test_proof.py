from __future__ import annotations

from io import BytesIO, StringIO
from typing import TYPE_CHECKING

import pytest

from proof_generation.basic_interpreter import ExecutionPhase
from proof_generation.claim import Claim
from proof_generation.deserialize import deserialize_instructions
from proof_generation.instruction import Instruction
from proof_generation.pattern import App, EVar, Exists, Implies, MetaVar, Mu, PrettyOptions, SVar, Symbol
from proof_generation.pretty_printing_interpreter import PrettyPrintingInterpreter
from proof_generation.proof import ProofExp, ProofThunk
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

    assert Implies(phi0, phi0).instantiate({0: phi1}) == Implies(phi1, phi1)
    assert Implies(phi0, phi1).instantiate({2: phi0_ef0}) == Implies(phi0, phi1)

    assert App(phi0, phi0).instantiate({0: phi1}) == App(phi1, phi1)
    assert App(phi0, phi1).instantiate({2: phi0_ef0}) == App(phi0, phi1)

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
    phi0_implies_phi0 = Implies(phi0, phi0)
    prop = Propositional()
    ProofThunk(
        prop.modus_ponens(
            ProofThunk(
                prop.modus_ponens(
                    ProofThunk(
                        prop.dynamic_inst(prop.prop2(), {1: phi0_implies_phi0, 2: phi0}),
                        Implies(
                            Implies(phi0, Implies(phi0_implies_phi0, phi0)),
                            Implies(Implies(phi0, phi0_implies_phi0), Implies(phi0, phi0)),
                        ),
                    ),
                    ProofThunk(
                        prop.dynamic_inst(prop.prop1(), {1: phi0_implies_phi0}),
                        Implies(phi0, Implies(phi0_implies_phi0, phi0)),
                    ),
                ),
                Implies(Implies(phi0, phi0_implies_phi0), Implies(phi0, phi0)),
            ),
            prop.dynamic_inst(prop.prop1(), {1: phi0}),
        ),
        Implies(phi0, phi0),
    )(StatefulInterpreter(phase=ExecutionPhase.Proof))


def uncons_metavar_instrs(id: int) -> list[int]:
    return [Instruction.CleanMetaVar, id]


def test_prove_imp_refl() -> None:
    out = BytesIO()
    phi0 = MetaVar(0)
    phi0_implies_phi0 = Implies(phi0, phi0)
    prop = Propositional()
    proved = prop.publish_proof(prop.imp_refl())
    interpreter = SerializingInterpreter(phase=ExecutionPhase.Proof, claims=[Claim(phi0_implies_phi0)], out=out)
    assert proved(interpreter).conclusion == phi0_implies_phi0
    # fmt: off
    assert bytes(out.getbuffer()) == bytes([
        *uncons_metavar_instrs(0),             # Stack: ph0
        *uncons_metavar_instrs(0),             # Stack: ph0; ph0
        Instruction.Implies,                   # Stack: ph0 -> ph0
        *uncons_metavar_instrs(0),             # Stack: ph0 -> ph0; ph0
        Instruction.Prop2,                     # Stack: ph0 -> ph0; ph0; prop2
        Instruction.Instantiate, 2, 2, 1,      # Stack: p1=[(ph0 -> ((ph0 -> ph0) -> ph0)) -> ((ph0 -> (ph0 -> ph0)) -> (ph0 -> ph0))]
        *uncons_metavar_instrs(0),             # Stack: p1; ph0;
        *uncons_metavar_instrs(0),             # Stack: p1; ph0; ph0;
        Instruction.Implies,                   # Stack: p1; ph0 -> ph0;
        Instruction.Prop1,                     # Stack: p1; ph0 -> ph0; prop1
        Instruction.Instantiate, 1, 1,         # Stack: p1; [p2: (ph0 -> ((ph0 -> ph0) -> ph0)) ]
        Instruction.ModusPonens,               # Stack: [p3: ((ph0 -> (ph0 -> ph0)) -> (ph0 -> ph0))
        *uncons_metavar_instrs(0),             # Stack: p3; ph0;
        Instruction.Prop1,                     # Stack: p3; ph0; prop1
        Instruction.Instantiate, 1, 1,         # Stack: p3; ph0 -> (ph0 -> ph0)
        Instruction.ModusPonens,               # Stack: phi0 -> phi0
        Instruction.Publish,
    ])
    # fmt: on


proofs = [(method, ExecutionPhase.Proof) for method in range(len(Propositional()._proof_expressions))]


@pytest.mark.parametrize('test', proofs)
def test_deserialize_proof(test: tuple[int, ExecutionPhase]) -> None:
    pretty_options = PrettyOptions(simplify_instantiations=True)
    (target, phase) = test
    # Serialize the target and deserialize the resulting bytes with the PrettyPrintingInterpreter
    out_ser = BytesIO()
    interpreter_ser = SerializingInterpreter(phase=phase, out=out_ser)
    _ = Propositional()._proof_expressions[target](interpreter_ser)
    out_ser_deser = StringIO()
    interpreter_ser_deser = PrettyPrintingInterpreter(phase=phase, out=out_ser_deser, pretty_options=pretty_options)
    deserialize_instructions(out_ser.getvalue(), interpreter_ser_deser)

    # Prettyprint the proof directly, but omit notation
    out_pretty = StringIO()
    interpreter_pretty = PrettyPrintingInterpreter(phase=phase, out=out_pretty, pretty_options=pretty_options)
    _ = Propositional()._proof_expressions[target](interpreter_pretty)

    assert out_pretty.getvalue() == out_ser_deser.getvalue()


claims = [(claim, ExecutionPhase.Claim) for claim in Propositional()._claims]


@pytest.mark.parametrize('test', claims)
def test_deserialize_claim(test: tuple[Pattern, ExecutionPhase]) -> None:
    pretty_options = PrettyOptions(simplify_instantiations=True)
    (target, phase) = test
    # Serialize the target and deserialize the resulting bytes with the PrettyPrintingInterpreter
    out_ser = BytesIO()
    interpreter_ser = SerializingInterpreter(phase=phase, out=out_ser)
    _ = interpreter_ser.pattern(target)
    out_ser_deser = StringIO()
    interpreter_ser_deser = PrettyPrintingInterpreter(phase=phase, out=out_ser_deser, pretty_options=pretty_options)
    deserialize_instructions(out_ser.getvalue(), interpreter_ser_deser)

    # Prettyprint the claim directly, but omit notation
    out_pretty = StringIO()
    interpreter_pretty = PrettyPrintingInterpreter(phase=phase, out=out_pretty, pretty_options=pretty_options)
    _ = interpreter_pretty.pattern(target)

    assert out_pretty.getvalue() == out_ser_deser.getvalue()


@pytest.mark.parametrize(
    'pats',
    [
        [],
        [MetaVar(0), MetaVar(1)],
        [Symbol('a')],
        [MetaVar(1, (EVar(0), EVar(1)), (SVar(1),))],
    ],
)
def test_serialization(pats: list[Pattern]) -> None:
    interpreter_ser = SerializingInterpreter(
        phase=ExecutionPhase.Gamma, claims=[Claim(pattern) for pattern in pats], out=BytesIO(), claim_out=BytesIO(), proof_out=BytesIO()
    )
    proof_exp = ProofExp(axioms=pats, claims=pats)
    proof_exp._proof_expressions = [proof_exp.load_axiom(pat) for pat in pats]
    assert interpreter_ser.memory == []
    assert [claim.pattern for claim in interpreter_ser.claims] == pats
    assert interpreter_ser.stack == []
    proof_exp.execute_gamma_phase(interpreter_ser, False)
    assert [proved.conclusion for proved in interpreter_ser.memory] == pats
    assert [claim.pattern for claim in interpreter_ser.claims] == pats
    assert interpreter_ser.stack == pats
    interpreter_ser.into_claim_phase()
    proof_exp.execute_claims_phase(interpreter_ser, False)
    assert [proved.conclusion for proved in interpreter_ser.memory] == pats
    assert [claim.pattern for claim in interpreter_ser.claims] == pats
    assert list(reversed(interpreter_ser.stack)) == pats
    interpreter_ser.into_proof_phase()
    proof_exp.execute_proofs_phase(interpreter_ser)
    assert [proved.conclusion for proved in interpreter_ser.memory] == pats
    assert interpreter_ser.claims == []
    assert [proved.conclusion for proved in interpreter_ser.stack] == pats
