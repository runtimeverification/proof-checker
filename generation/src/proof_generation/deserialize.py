from enum import Enum
from io import BytesIO, StringIO, TextIOBase

from pprint import PrettyPrinter
from proof_generation.instruction import Instruction
from proof_generation.proof import Pattern, PrettyPrintingInterpreter, SerializingInterpreter, MetaVar, Implication, Claim
from proof_generation.proofs.propositional import Propositional


class ExecutionPhase(Enum):
    Claim = 0
    Proof = 1

def deserialize_instructions(data, interpreter: PrettyPrintingInterpreter):
    phase = ExecutionPhase.Claim

    assert isinstance(interpreter, PrettyPrintingInterpreter)

    index = 0

    def next_byte():
        nonlocal index
        if index == len(data):
            return None
        ret = data[index]
        index += 1
        return ret

    while byte := next_byte():
        instruction = Instruction(byte)
        #print(instruction)

        if instruction == Instruction.List:
            length = next_byte()
            if length != 0:
                raise ValueError("Length was supposed to be zero.")
            interpreter.stack.append(())

        elif instruction == Instruction.EVar:
            id = next_byte()
            _evar = interpreter.evar(id)

        elif instruction == Instruction.SVar:
            id = next_byte()
            _svar = interpreter.svar(id)

        elif instruction == Instruction.Symbol:
            id = next_byte()
            _symbol = interpreter.symbol(id)

        elif instruction == Instruction.Implication:
            right = interpreter.stack[-1]
            left = interpreter.stack[-2]
            _implication = interpreter.implies(left, right)

        elif instruction == Instruction.Application:
            right = interpreter.stack[-1]
            left = interpreter.stack[-2]
            _app = interpreter.app(left, right)

        elif instruction == Instruction.Exists:
            id = next_byte()
            subpattern = interpreter.stack[-1]
            _exists = interpreter.exists(id, subpattern)

        elif instruction == Instruction.Mu:
            id = next_byte()
            subpattern = interpreter.stack[-1]
            _mu = interpreter.mu(id, subpattern)

        elif instruction == Instruction.MetaVar:
            id = next_byte()
            app_ctxt_holes, negative, positive, s_fresh, e_fresh = reversed(interpreter.stack[-5:])
            _metavar = interpreter.metavar(id, e_fresh, s_fresh, positive, negative, app_ctxt_holes)

        elif instruction == Instruction.Prop1:
            _prop1 = interpreter.prop1()

        elif instruction == Instruction.Prop2:
            _prop2 = interpreter.prop2()

        elif instruction == Instruction.ModusPonens:
            right = interpreter.stack[-1]
            left = interpreter.stack[-2]
            _mp = interpreter.modus_ponens(left, right)

        elif instruction == Instruction.Instantiate:
            n = next_byte()
            keys = [next_byte() for _ in range(n)]
            values = interpreter.stack[-n:]

            delta = dict(zip(keys, values, strict=True))
            proved = interpreter.stack[-(n + 1)]

            print(delta, proved)
            interpreter.instantiate(proved, delta)

        elif instruction == Instruction.Pop:
            interpreter.stack.pop()

        elif instruction == Instruction.Save:
            term = interpreter.stack[-1]
            interpreter.save(len(interpreter.memory), term)

        elif instruction == Instruction.Load:
            id = next_byte()
            try:
                term = interpreter.memory[id]
                interpreter.load(id, term)
            except:
                raise ValueError("Invalid entry type for Load instruction.")

        elif instruction == Instruction.Publish:
            if phase == ExecutionPhase.Claim:
                claim = interpreter.stack[-1]
                interpreter.claims.append(claim)
                interpreter.publish_claim(claim)
            elif phase == ExecutionPhase.Proof:
                claim = interpreter.claims.pop()
                theorem = interpreter.stack[-1]
                interpreter.publish_claim(claim)
                if claim != theorem:
                    raise ValueError(f"This proof does not prove the requested claim: {claim}, theorem: {theorem}")

        else:
            raise NotImplementedError(f"Instruction: {instruction}")

    return interpreter


# out = BytesIO()
# prop = Propositional(SerializingInterpreter([], out))

# prop.phi0_implies_phi0()
# ser = out.getvalue()

# print(len(ser))

# log = StringIO()
# obj = deserialize_instructions(ser, PrettyPrintingInterpreter([], log))
# print(log.getvalue())
# print("######\n")
# PrettyPrinter().pprint(obj.stack)

out = BytesIO()
phi0 = MetaVar(0)
phi0_implies_phi0 = Implication(phi0, phi0)
prop = Propositional(SerializingInterpreter(claims=[Claim(phi0_implies_phi0)], out=out))
proved = prop.publish(prop.imp_reflexivity())