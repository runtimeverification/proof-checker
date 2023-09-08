from __future__ import annotations

from collections import UserDict
from typing import Any

from mm_transfer.metamath.ast import Metavariable


class Vardict(UserDict):
    """
    This dictionary simplifies checking that a Metavariable is in the dictionary.
    You can type just: "metavar in varidct" in both cases where metavar is a Metavariable
    and where it is a string. Same is for saving new items.
    """

    def __init__(self, __data: dict[str, Any] | None = None, expected: type | None = None) -> None:
        super().__init__(__data)
        self._expected = expected

    def __getitem__(self, __key: Metavariable | str) -> Any:
        if isinstance(__key, Metavariable):
            __key = __key.name
        return super().__getitem__(__key)

    def __setitem__(self, __key: Metavariable | str, __value: Any) -> None:
        if isinstance(__key, Metavariable):
            __key = __key.name
        if isinstance(self._expected, type) and not isinstance(__value, self._expected):
            raise TypeError(f'Expected {self._expected}, got {type(__value).__name__}')
        return super().__setitem__(__key, __value)
