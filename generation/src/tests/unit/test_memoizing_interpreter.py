from proof_generation.interpreter import ExecutionPhase
from proof_generation.optimizing_interpreters import MemoizingInterpreter
from proof_generation.pattern import MetaVar
from proof_generation.stateful_interpreter import StatefulInterpreter


def test_memoizing_interpreter() -> None:
    sub_interpreter = StatefulInterpreter(ExecutionPhase.Proof)
    memoizer = MemoizingInterpreter(sub_interpreter, {MetaVar(0), MetaVar(1)})

    memoizer.metavar(0)
    assert sub_interpreter.stack[-1] == MetaVar(0)

    cached_pattern = memoizer.pattern(MetaVar(1))
    assert isinstance(cached_pattern, MetaVar)
    assert cached_pattern.name == 1
    assert cached_pattern in sub_interpreter.memory

    cached_pattern = memoizer.pattern(MetaVar(2))
    assert isinstance(cached_pattern, MetaVar)
    assert cached_pattern.name == 2
    assert cached_pattern not in sub_interpreter.memory
