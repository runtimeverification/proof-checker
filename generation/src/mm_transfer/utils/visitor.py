from __future__ import annotations

from typing import TYPE_CHECKING, Generic, TypeVar, Union

if TYPE_CHECKING:
    from collections.abc import Callable
    from typing import Any


TreeT = TypeVar('TreeT', contravariant=True)
ResultT = TypeVar('ResultT')
ChildrenResultT = Union[ResultT, list[ResultT]]


class Visitor(Generic[TreeT, ResultT]):
    """
    A general visitor base class
    """

    def previsit_default(self, x: TreeT) -> None:
        return

    def visit_children_of_default(self, x: TreeT) -> list[ChildrenResultT[ResultT]]:
        return []

    def postvisit_default(self, x: TreeT, *args: ChildrenResultT[ResultT]) -> ResultT:
        return x  # type: ignore # TODO

    def visit(self, x: TreeT) -> ResultT:
        return x.visit(self)  # type: ignore

    def __getattr__(self, name: str) -> Callable[..., Any]:
        """
        When a node.visit is called, proxy_visit_* will be called first, which will:
        1. call previsit_*
        2. call visit_children_of_* to visit all children
        3. call postvisit_* (with return values of the children visits)
        """
        if name.startswith('previsit_'):
            return self.previsit_default
        elif name.startswith('visit_children_of_'):
            return self.visit_children_of_default
        elif name.startswith('postvisit_'):
            return self.postvisit_default
        elif name.startswith('proxy_visit_'):
            name = name[12:]

            def f(node: TreeT) -> ResultT:
                getattr(self, 'previsit_' + name)(node)
                children = getattr(self, 'visit_children_of_' + name)(node)
                return getattr(self, 'postvisit_' + name)(node, *children)  # type: ignore

            return f
        else:
            raise AttributeError(name)
