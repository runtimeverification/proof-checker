from proof_generation.aml import Instantiate, MetaVar
from proof_generation.interpreter import ExecutionPhase
from proof_generation.optimizing_interpreters import InstantiationOptimizer
from proof_generation.stateful_interpreter import StatefulInterpreter


def test_instantiation_optimizer() -> None:
    sub_interpreter = StatefulInterpreter(ExecutionPhase.Proof)
    optimizer = InstantiationOptimizer(sub_interpreter)

    optimizer.metavar(0)
    assert sub_interpreter.stack[-1] == MetaVar(0)
    assert isinstance(sub_interpreter.stack[-1], MetaVar)

    inst = optimizer.metavar(1)
    untransformed = optimizer.instantiate_pattern(optimizer.metavar(0), {0: inst})
    # TODO: The overriden equality checking makes this annoying.
    # We need to have a separate methods for checking equality modulo Instantiations.
    # The silent desugaring will also lead to perfomance issues.
    assert isinstance(untransformed, Instantiate)
    assert isinstance(sub_interpreter.stack[-1], Instantiate)
    assert sub_interpreter.stack[-1] == MetaVar(1)

    inst = optimizer.metavar(0)
    untransformed = optimizer.instantiate_pattern(optimizer.metavar(0), {0: inst})
    assert isinstance(untransformed, Instantiate)
    assert isinstance(sub_interpreter.stack[-1], Instantiate)
    assert sub_interpreter.stack[-1] == MetaVar(0)

    untransformed = optimizer.instantiate_pattern(optimizer.metavar(0), {})
    assert isinstance(untransformed, Instantiate)
    assert isinstance(sub_interpreter.stack[-1], MetaVar)
    assert sub_interpreter.stack[-1] == MetaVar(0)
