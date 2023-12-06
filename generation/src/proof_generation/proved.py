from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from proof_generation.pattern import Pattern


class ExecutionPhase(Enum):
    Gamma = 0
    Claim = 1
    Proof = 2


#  TODO Get rif of this wrapper type
@dataclass
class Proved:
    conclusion: Pattern

    def __str__(self) -> str:
        return str(self.conclusion)
