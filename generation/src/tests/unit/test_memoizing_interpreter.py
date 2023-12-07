from proof_generation.interpreter import ExecutionPhase
from proof_generation.optimizing_interpreters import MemoizingInterpreter
from proof_generation.pattern import MetaVar
from proof_generation.instruction import Instruction
from proof_generation.serializing_interpreter import SerializingInterpreter
from tests.unit.test_proof import uncons_metavar_instrs
from io import BytesIO

def test_memoizing_interpreter() -> None:
    out_interp = BytesIO()
    sub_interpreter = SerializingInterpreter(ExecutionPhase.Proof, out=out_interp)
    memoizer = MemoizingInterpreter(sub_interpreter, {MetaVar(0), MetaVar(1)})

    # check updating the sub_interpreter's state
    memoizer.metavar(0)
    assert sub_interpreter.stack[-1] == MetaVar(0)
    # memoizer only updates the .pattern() instruction
    assert sub_interpreter.stack[-1] not in sub_interpreter.memory

    # check loading a memoized pattern that is fresh to the sub_interpreter
    pattern = MetaVar(1)
    assert pattern not in sub_interpreter.memory
    cached_pattern = memoizer.pattern(MetaVar(1))
    assert pattern in sub_interpreter.memory
    assert sub_interpreter.stack[-1] == pattern

    # check loading the same memoized pattern again
    cached_pattern_2 = memoizer.pattern(MetaVar(1))
    assert cached_pattern_2 == cached_pattern

    # check loading a non-memoized pattern fresh to the sub_interpreter
    unsaved_pattern = memoizer.pattern(MetaVar(2))
    assert isinstance(unsaved_pattern, MetaVar)
    assert unsaved_pattern.name == 2
    assert unsaved_pattern not in sub_interpreter.memory

    # check that the stacking works
    assert sub_interpreter.stack ==[
        MetaVar(0),
        MetaVar(1),
        MetaVar(1),
        MetaVar(2)
    ]

    # check memoization in the stream
    assert out_interp.getvalue() == bytes([
        *uncons_metavar_instrs(0),
        *uncons_metavar_instrs(1),
        Instruction.Save,
        Instruction.Load, 0,
        *uncons_metavar_instrs(2)
    ])
