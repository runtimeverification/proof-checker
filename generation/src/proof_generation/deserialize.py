from enum import Enum
from io import BytesIO
from pprint import PrettyPrinter

from proof_generation.instruction import Instruction
from proof_generation.proof import (
    Application,
    ESubst,
    EVar,
    Exists,
    Implication,
    Instantiate,
    MetaVar,
    ModusPonens,
    Mu,
    Pattern,
    Proof,
    Prop1,
    Prop2,
    SVar,
    Symbol,
)
from proof_generation.proofs.propositional import Propositional


class ExecutionPhase(Enum):
    Claim = 0
    Proof = 1


class Stack:
    def __init__(self):
        self.stack = []

    def push(self, item):
        self.stack.append(item)

    def pop(self):
        return self.stack.pop()

    def last(self):
        return self.stack[-1]

    def is_empty(self):
        return len(self.stack) == 0


class Memory:
    def __init__(self):
        self.entries = []

    def push(self, entry):
        self.entries.append(entry)

    def get(self, index):
        return self.entries[index]


class Claims:
    def __init__(self):
        self.claims = []

    def push(self, claim):
        self.claims.append(claim)

    def pop(self):
        return self.claims.pop()


def deserialize_instructions(data):
    stack = Stack()
    memory = Memory()
    claims = Claims()
    phase = ExecutionPhase.Claim

    def pop_stack_pattern(stack):
        return stack.pop()

    def pop_stack_proved(stack):
        return stack.pop()

    index = 0

    def next_byte():
        nonlocal index
        if index == len(data):
            return None
        # print(index)
        ret = data[index]
        index += 1
        return ret

    pp = PrettyPrinter()

    while byte := next_byte():
        instr_u32 = Instruction(byte)
        pp.pprint(instr_u32)
        pp.pprint(stack.stack)

        if instr_u32 == Instruction.List:
            length = next_byte()
            if length != 0:
                raise ValueError("Length was supposed to be zero.")
            stack.push(())

        elif instr_u32 == Instruction.EVar:
            id = next_byte()
            stack.push(EVar(id))

        elif instr_u32 == Instruction.SVar:
            id = next_byte()
            stack.push(SVar(id))

        elif instr_u32 == Instruction.Symbol:
            id = next_byte()
            stack.push(Symbol(id))

        elif instr_u32 == Instruction.Implication:
            right = pop_stack_pattern(stack)
            left = pop_stack_pattern(stack)
            stack.push(Implication(left, right))

        elif instr_u32 == Instruction.Application:
            right = pop_stack_pattern(stack)
            left = pop_stack_pattern(stack)
            stack.push(Application(left, right))

        elif instr_u32 == Instruction.Exists:
            id = next_byte()
            subpattern = pop_stack_pattern(stack)
            stack.push(Exists(EVar(id), subpattern))

        elif instr_u32 == Instruction.Mu:
            id = next_byte()
            subpattern = pop_stack_pattern(stack)
            stack.push(Mu(SVar(id), subpattern))

        elif instr_u32 == Instruction.MetaVar:
            id = next_byte()
            application_context = pop_stack_pattern(stack)
            negative = pop_stack_pattern(stack)
            positive = pop_stack_pattern(stack)
            s_fresh = pop_stack_pattern(stack)
            e_fresh = pop_stack_pattern(stack)
            stack.push(MetaVar(id, e_fresh, s_fresh, positive, negative, application_context))

        elif instr_u32 == Instruction.ESubst:
            evar_id = next_byte()
            pattern = pop_stack_pattern(stack)
            plug = pop_stack_pattern(stack)
            stack.push(ESubst(pattern, evar_id, plug))

        elif instr_u32 == Instruction.Prop1:
            stack.push(Prop1())

        elif instr_u32 == Instruction.Prop2:
            stack.push(Prop2())

        elif instr_u32 == Instruction.ModusPonens:
            right = pop_stack_proved(stack)
            left = pop_stack_proved(stack)
            stack.push(ModusPonens(left, right))
        elif instr_u32 == Instruction.Instantiate:
            id = next_byte()
            plug = pop_stack_pattern(stack)
            metaterm = stack.pop()
            if isinstance(metaterm, (Pattern, Proof)):
                stack.push(Instantiate(metaterm, id, plug))
            else:
                raise ValueError(f'Cannot Instantiate {type(metaterm)}.')

        elif instr_u32 == Instruction.Pop:
            stack.pop()

        elif instr_u32 == Instruction.Save:
            entry = stack.last()
            if isinstance(entry, Pattern):
                memory.push((False, entry))
            elif isinstance(entry, Proof):
                memory.push((True, entry))
            else:
                raise ValueError("Cannot Save lists.")

        elif instr_u32 == Instruction.Load:
            at = next_byte()
            try:
                entry = memory.get(at)
                stack.push(entry[1])
            except:
                raise ValueError("Invalid entry type for Load instruction.")

        elif instr_u32 == Instruction.Publish:
            if phase == ExecutionPhase.Claim:
                claim = pop_stack_pattern(stack)
                claims.push(claim)
            elif phase == ExecutionPhase.Proof:
                claim = claims.pop()
                theorem = pop_stack_proved(stack)
                if claim != theorem:
                    raise ValueError(f"This proof does not prove the requested claim: {claim}, theorem: {theorem}")

        else:
            raise NotImplementedError(f"Instruction: {instr_u32}")

    return stack, memory, claims


prop = Propositional()
out = BytesIO()
prop.imp_reflexivity().serialize({prop.phi0, prop.phi0_implies_phi0}, set(), [], [prop.phi0_implies_phi0], out)
ser = bytes(out.getbuffer())

print(len(ser))

obj = deserialize_instructions(ser)

print(obj.conclusion())
