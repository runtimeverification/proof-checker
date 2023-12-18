from __future__ import annotations

from typing import TYPE_CHECKING

from .basic_interpreter import BasicInterpreter
from .interpreter_transformer import InterpreterTransformer
from .stateful_interpreter import StatefulInterpreter

if TYPE_CHECKING:
    from collections.abc import Mapping

    from ..aml import Pattern
    from ..proved import Proved
    from .interpreter import Interpreter


class InstantiationOptimizer(InterpreterTransformer):
    def __init__(self, sub_interpreter: Interpreter):
        super().__init__(sub_interpreter)

    def instantiate(self, proved: Proved, delta: dict[int, Pattern]) -> Proved:
        b_interp = BasicInterpreter(self.phase)
        ret = b_interp.instantiate(proved, delta)
        if len(delta):
            self.sub_interpreter.instantiate(proved, delta)
        return ret

    def instantiate_pattern(self, pattern: Pattern, delta: Mapping[int, Pattern]) -> Pattern:
        b_interp = BasicInterpreter(self.phase)
        ret = b_interp.instantiate_pattern(pattern, delta)
        if len(delta):
            self.sub_interpreter.instantiate_pattern(pattern, delta)
        return ret


class MemoizingInterpreter(InterpreterTransformer):
    def __init__(self, sub_interpreter: Interpreter, patterns_for_memoization: set[Pattern]):
        super().__init__(sub_interpreter)
        self._patterns_for_memoization = patterns_for_memoization

    def pattern(self, p: Pattern) -> Pattern:
        assert isinstance(self.core_interpreter, StatefulInterpreter)
        if p in self.core_interpreter.memory:
            self.load(str(p), p)
            return p
        elif p in self._patterns_for_memoization:
            ret = super().pattern(p)
            self.save(repr(p), p)
            return ret
        else:
            return super().pattern(p)
