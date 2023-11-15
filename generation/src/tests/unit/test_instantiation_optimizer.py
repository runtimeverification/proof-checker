from proof_generation.basic_interpreter import ExecutionPhase
from proof_generation.instantiation_optimizer import InstantiationOptimizer
from proof_generation.pattern import Instantiate, MetaVar
from proof_generation.stateful_interpreter import StatefulInterpreter


def test_instantiation_optimizer() -> None:
    output_interpreter = StatefulInterpreter(ExecutionPhase.Proof)
    optimizer = InstantiationOptimizer(output_interpreter)

    optimizer.metavar(0)
    assert output_interpreter.stack[-1] == MetaVar(0)
    assert isinstance(output_interpreter.stack[-1], MetaVar)

    inst = optimizer.metavar(1)
    untransformed = optimizer.instantiate_pattern(optimizer.metavar(0), {0: inst})
    # TODO: The overriden equality checking makes this annoying.
    # We need to have a separate methods for checking equality modulo Instantiations.
    # The silent desugaring will also lead to perfomance issues.
    assert isinstance(untransformed, Instantiate)
    assert isinstance(output_interpreter.stack[-1], Instantiate)
    assert output_interpreter.stack[-1] == MetaVar(1)

    inst = optimizer.metavar(0)
    untransformed = optimizer.instantiate_pattern(optimizer.metavar(0), {0: inst})
    assert isinstance(untransformed, Instantiate)
    assert isinstance(output_interpreter.stack[-1], Instantiate)
    assert output_interpreter.stack[-1] == MetaVar(0)

    untransformed = optimizer.instantiate_pattern(optimizer.metavar(0), {})
    assert isinstance(untransformed, Instantiate)
    assert isinstance(output_interpreter.stack[-1], MetaVar)
    assert output_interpreter.stack[-1] == MetaVar(0)
