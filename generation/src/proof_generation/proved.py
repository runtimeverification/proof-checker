from __future__ import annotations

from dataclasses import dataclass
from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from proof_generation.pattern import Pattern


@dataclass
class Proved:
    conclusion: Pattern

    def assertc(self, pattern: Pattern) -> Proved:
        assert self.conclusion == pattern
        return self

    def __str__(self) -> str:
        return str(self.conclusion)
