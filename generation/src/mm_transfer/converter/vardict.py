from __future__ import annotations
from collections import UserDict
from typing import Any

from mm_transfer.metamath.ast import Metavariable


class Vardict(UserDict):

    def __init__(self, __data: dict[str, Any] | None = None, expected: type = Any) -> None:
        super().__init__(__data)
        self._expected = expected

    def __getitem__(self, __key: Metavariable | str) -> Any:
        if isinstance(__key, Metavariable):
            __key = __key.name
        return super().__getitem__(__key)

    def __setitem__(self, __key: Metavariable | str, __value: Any) -> None:
        if isinstance(__key, Metavariable):
            __key = __key.name
        if not isinstance(__value, self._expected):
            raise TypeError(f'Expected {self._expected}, got {type(__value).__name__}')
        return super().__setitem__(__key, __value)
