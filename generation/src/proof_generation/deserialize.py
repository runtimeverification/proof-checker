from enum import Enum
from typing import Any, Optional

from proof_generation.instruction import Instruction
from proof_generation.proof import Pattern, PrettyPrintingInterpreter, Proved


class ExecutionPhase(Enum):
    Claim = 0
    Proof = 1


class DeserializingException(Exception):
    pass


def deserialize_instructions(
    data: Any, interpreter: PrettyPrintingInterpreter, phase: ExecutionPhase
) -> PrettyPrintingInterpreter:
    assert isinstance(interpreter, PrettyPrintingInterpreter)

    index = 0

    def next_byte(err_msg: Optional[str] = None) -> Optional[int]:
        nonlocal index
        if index == len(data):
            if err_msg is None:
                return None
            raise DeserializingException(err_msg)
        ret = data[index]
        index += 1
        return ret

    while byte := next_byte():
        instruction = Instruction(byte)

        if instruction == Instruction.List:
            length = next_byte('Expected list length.')
            if length != 0:
                raise ValueError('Length was supposed to be zero.')
            interpreter.stack.append(())  # type: ignore

        elif instruction == Instruction.EVar:
            id = next_byte('Expected EVar id.')
            _ = interpreter.evar(id)

        elif instruction == Instruction.SVar:
            id = next_byte('Expected SVar id.')
            _ = interpreter.svar(id)

        elif instruction == Instruction.Symbol:
            id = next_byte('Expected Symbol id.')
            _ = interpreter.symbol(id)

        elif instruction == Instruction.Implication:
            right = interpreter.stack[-1]
            left = interpreter.stack[-2]
            _ = interpreter.implies(left, right)

        elif instruction == Instruction.Application:
            right = interpreter.stack[-1]
            left = interpreter.stack[-2]
            _ = interpreter.app(left, right)

        elif instruction == Instruction.Exists:
            id = next_byte('Expected Exists binder id.')
            subpattern = interpreter.stack[-1]
            _ = interpreter.exists(id, subpattern)

        elif instruction == Instruction.Mu:
            id = next_byte('Expected Mu binder id.')
            subpattern = interpreter.stack[-1]
            _ = interpreter.mu(id, subpattern)

        elif instruction == Instruction.MetaVar:
            id = next_byte('Expected MetaVar id.')
            app_ctxt_holes, negative, positive, s_fresh, e_fresh = reversed(interpreter.stack[-5:])
            _ = interpreter.metavar(id, e_fresh, s_fresh, positive, negative, app_ctxt_holes)
            interpreter.stack = interpreter.stack[0:-6] + [interpreter.stack[-1]]

        elif instruction == Instruction.Prop1:
            _ = interpreter.prop1()

        elif instruction == Instruction.Prop2:
            _ = interpreter.prop2()

        elif instruction == Instruction.Prop3:
            _ = interpreter.prop3()

        elif instruction == Instruction.ModusPonens:
            right = interpreter.stack[-1]
            left = interpreter.stack[-2]
            _ = interpreter.modus_ponens(left, right)

        elif instruction == Instruction.Instantiate:
            n = next_byte('Expected number of instantiations.')
            keys = [next_byte() for _ in range(n)]
            values = reversed(interpreter.stack[-n:])

            delta = dict(reversed(list(zip(keys, values, strict=True))))
            target = interpreter.stack[-(n + 1)]

            if isinstance(target, Proved):
                interpreter.instantiate(target, delta)
            else:
                assert isinstance(target, Pattern), f'Trying to instantiate term of inadequate type {type(target)}.'
                interpreter.instantiate_notation(target, delta)

        elif instruction == Instruction.Pop:
            interpreter.stack.pop()

        elif instruction == Instruction.Save:
            term = interpreter.stack[-1]
            interpreter.save(len(interpreter.memory), term)

        elif instruction == Instruction.Load:
            id = next_byte('Expected index for Load instruction')
            try:
                term = interpreter.memory[id]
                interpreter.load(id, term)
            except BaseException:
                raise ValueError('Invalid entry type for Load instruction.') from None

        elif instruction == Instruction.Publish:
            if phase == ExecutionPhase.Claim:
                claim = interpreter.stack[-1]
                interpreter.claims.append(claim)  # type: ignore
                interpreter.publish_claim(claim)
            elif phase == ExecutionPhase.Proof:
                claim = interpreter.claims.pop()  # type: ignore
                theorem = interpreter.stack[-1]
                interpreter.publish_claim(claim)
                if claim != theorem:
                    raise ValueError(f'This proof does not prove the requested claim: {claim}, theorem: {theorem}')

        else:
            raise NotImplementedError(f'Instruction: {instruction}')

    return interpreter
