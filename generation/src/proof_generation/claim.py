from __future__ import annotations

from dataclasses import dataclass
from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from proof_generation.aml import Pattern


@dataclass
class Claim:
    pattern: Pattern
