from __future__ import annotations

from kore_transfer.kore_converter import LanguageSemantics

from typing import TYPE_CHECKING


def test_module_creation():
    semantics = LanguageSemantics(None)
    with semantics as definition:
        test_name = 'test_module'
        m = definition.module(test_name)

        assert m.name == test_name
        assert len(definition.modules) == 1
        assert m in definition.modules
