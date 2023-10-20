from __future__ import annotations

from typing import TYPE_CHECKING, Any

from proof_generation.basic_interpreter import ExecutionPhase
from proof_generation.instruction import Instruction
from proof_generation.pattern import Pattern
from proof_generation.proved import Proved

if TYPE_CHECKING:
    from proof_generation.pretty_printing_interpreter import PrettyPrintingInterpreter


class DeserializingException(Exception):
    pass


def deserialize_instructions(data: Any, interpreter: PrettyPrintingInterpreter) -> None:
    index = 0

    def next_byte(err_msg: str | None = None) -> int | None:
        nonlocal index
        if index == len(data):
            if err_msg is None:
                return None
            raise DeserializingException(err_msg)
        ret = data[index]
        index += 1
        return ret

    def read_list() -> tuple[int, ...]:
        length = next_byte('Expected list length')
        assert length is not None

        res = []
        for i in range(length):
            elem = next_byte(f'Expected {i}-th element of list')
            assert elem is not None
            res.append(elem)

        return tuple(res)

    while byte := next_byte():
        instruction = Instruction(byte)

        if instruction == Instruction.EVar:
            id = next_byte('Expected EVar id.')
            _ = interpreter.evar(id)

        elif instruction == Instruction.SVar:
            id = next_byte('Expected SVar id.')
            _ = interpreter.svar(id)

        elif instruction == Instruction.Symbol:
            id = next_byte('Expected Symbol id.')
            _ = interpreter.symbol(str(id))

        elif instruction == Instruction.Implies:
            right = interpreter.stack[-1]
            left = interpreter.stack[-2]
            _ = interpreter.implies(left, right)

        elif instruction == Instruction.App:
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

        elif instruction == Instruction.ESubst:
            evar_id = next_byte('Expected evar_id.')
            pattern = interpreter.stack[-1]
            plug = interpreter.stack[-1]
            interpreter.esubst(evar_id, pattern, plug)

        elif instruction == Instruction.SSubst:
            svar_id = next_byte('Expected svar_id.')
            pattern = interpreter.stack[-1]
            plug = interpreter.stack[-1]
            interpreter.ssubst(svar_id, pattern, plug)

        elif instruction == Instruction.MetaVar:
            id = next_byte('Expected MetaVar id.')
            e_fresh, s_fresh, positive, negative, app_ctxt_holes = (read_list() for _ in range(5))
            _ = interpreter.metavar(id, e_fresh, s_fresh, positive, negative, app_ctxt_holes)

        elif instruction == Instruction.CleanMetaVar:
            id = next_byte('Expected MetaVar id.')
            _ = interpreter.metavar(id, (), (), (), (), ())

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
            assert n is not None

            keys = [next_byte() for _ in range(n)]
            target = interpreter.stack[-1]
            values = reversed(interpreter.stack[-(n + 1) : -1])

            delta = dict(reversed(list(zip(keys, values, strict=True))))

            if isinstance(target, Proved):
                interpreter.instantiate(target, delta)
            elif isinstance(target, Pattern):
                interpreter.instantiate_pattern(target, delta)
            else:
                raise DeserializingException(f'Cannot instantiate term {target}.')

        elif instruction == Instruction.Pop:
            interpreter.pop(interpreter.stack[-1])

        elif instruction == Instruction.Save:
            term = interpreter.stack[-1]
            interpreter.save(str(len(interpreter.memory)), term)

        elif instruction == Instruction.Load:
            id = next_byte('Expected index for Load instruction')
            assert id is not None
            if id >= len(interpreter.memory):
                raise DeserializingException(f'Invalid index {id} for Load instruction.')
            interpreter.load(str(id), interpreter.memory[id])

        elif instruction == Instruction.Publish:
            if interpreter.phase == ExecutionPhase.Claim:
                pattern = interpreter.stack[-1]
                assert isinstance(pattern, Pattern)
                interpreter.publish_claim(pattern)
            elif interpreter.phase == ExecutionPhase.Proof:
                claim = interpreter.claims.pop()
                theorem = interpreter.stack[-1]
                assert isinstance(theorem, Proved)
                interpreter.publish_claim(claim.pattern)
                if claim.pattern != theorem.conclusion:
                    raise DeserializingException(
                        f'This proof does not prove the requested claim: {claim}, theorem: {theorem}'
                    )
        else:
            raise NotImplementedError(f'Unknown instruction: {instruction}')
