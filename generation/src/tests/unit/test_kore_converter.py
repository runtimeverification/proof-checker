from __future__ import annotations

from kore_transfer.kore_converter import LanguageSemantics


def test_module_creation() -> None:
    semantics = LanguageSemantics()
    with semantics as definition:
        test_name = 'test_module'
        m = definition.module(test_name)

        assert m.name == test_name
        assert len(definition.modules) == 1
        assert m in definition.modules
