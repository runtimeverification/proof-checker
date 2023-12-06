from proof_generation.interpreter import ExecutionPhase
from proof_generation.optimizing_interpreters import MemoizingInterpreter
from proof_generation.pattern import MetaVar
from proof_generation.stateful_interpreter import StatefulInterpreter


def test_memoizing_interpreter() -> None:
    sub_interpreter = StatefulInterpreter(ExecutionPhase.Proof)
    memoizer = MemoizingInterpreter(sub_interpreter, {MetaVar(0), MetaVar(1)})

    # check updating the sub_interpreter's state
    memoizer.metavar(0)
    assert sub_interpreter.stack[-1] == MetaVar(0)

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
    cached_pattern = memoizer.pattern(MetaVar(2))
    assert isinstance(cached_pattern, MetaVar)
    assert cached_pattern.name == 2
    assert cached_pattern not in sub_interpreter.memory
