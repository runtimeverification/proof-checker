from __future__ import annotations

from dataclasses import dataclass
from typing import TYPE_CHECKING

from mypy_extensions import VarArg

if TYPE_CHECKING:
    from collections.abc import Callable

    import proof_generation.pattern as nf


@dataclass(frozen=True)
class Notation:
    name: str
    args: tuple[str, ...]
    type_check: Callable[[VarArg(nf.Pattern)], bool]
    callable: Callable[[VarArg(nf.Pattern)], nf.Pattern]

    def __call__(self, *args: nf.Pattern) -> nf.Pattern:
        assert self.type_check(*args), f'Invalid arguments for {self.name}'
        return self.callable(*args)


@dataclass(frozen=True)
class Axiom:
    name: str
    args: tuple[str, ...]
    type_check: Callable[[VarArg(nf.Pattern)], bool]
    pattern: nf.Pattern


@dataclass(frozen=True)
class ComplexAxiom(Axiom):
    name: str
    args: tuple[str, ...]
    type_check: Callable[[VarArg(nf.Pattern)], bool]
    pattern: nf.Pattern
    antecedents: tuple[nf.Pattern, ...]
