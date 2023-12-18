from __future__ import annotations

from dataclasses import dataclass
from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from proof_generation.aml import Pattern


#  TODO Get rif of this wrapper type
@dataclass
class Proved:
    conclusion: Pattern

    def __str__(self) -> str:
        return str(self.conclusion)
