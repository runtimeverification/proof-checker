from __future__ import annotations

from enum import IntEnum
from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from collections.abc import Iterator


class Instruction(IntEnum):
    List = 0x01

    # Patterns
    EVar = 0x02
    SVar = 0x03
    Symbol = 0x04
    Implication = 0x05
    Application = 0x06
    Mu = 0x07
    Exists = 0x10

    # Meta Patterns
    MetaVar = 0x09
    ESubst = 0x0A
    SSubst = 0x0B

    # Axiom Schemas
    Prop1 = 0x0C
    Prop2 = 0x0D  # TODO: Fix numbering
    Prop3 = 0x0E  # TODO: Fix numbering

    Quantifier = 0x0F
    PropagationOr = 0x10
    PropagationExists = 0x11
    PreFixpoint = 0x12
    Existance = 0x13
    Singleton = 0x14

    # Inference rules
    ModusPonens = 0x15
    Generalization = 0x16
    Frame = 0x17
    Substitution = 0x18
    KnasterTarski = 0x19

    # Meta Incference rules
    Instantiate = 0x1A

    # Stack Manipulation
    Pop = 0x1B

    # Memory Manipulation
    Save = 0x1C
    Load = 0x1D

    # Journal Manipulation
    Publish = 0x1E


def pack(input: Iterator[int]) -> bytes:
    """Render into a binary representation.
    For now, we restrict ourselves to 256 distinct symbols, element
    variables, set variables, and metavariables, considered separately,
    and 256 memory locations.
    """

    return bytes(input)
