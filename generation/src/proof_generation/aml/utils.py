from __future__ import annotations

from dataclasses import dataclass
from typing import TYPE_CHECKING

from frozendict import frozendict

from .syntax import App, ESubst, EVar, Exists, Implies, Instantiate, MetaVar, Mu, Pattern, SSubst, SVar, Symbol

if TYPE_CHECKING:
    from collections.abc import Mapping

    from .syntax import InstantiationDict, PrettyOptions

"""
Matching
========
"""


def match_single(
    pattern: Pattern, instance: Pattern, extend: dict[int, Pattern] | None = None
) -> dict[int, Pattern] | None:
    ret: dict[int, Pattern] | None
    ret = extend if extend else {}

    if isinstance(pattern, MetaVar):
        id = pattern.name
        if id in ret:
            if ret[id] != instance:
                return None
        else:
            if not pattern.can_be_replaced_by(instance):
                return None
            ret[id] = instance
        return ret
    if (pat_imp := Implies.unwrap(pattern)) and (inst_imp := Implies.unwrap(instance)):
        ret = match_single(pat_imp[0], inst_imp[0], ret)
        if ret is None:
            return None
        return match_single(pat_imp[1], inst_imp[1], ret)
    # The following three cases are more verbose because a 0 returned by the
    # deconstruct is still interpreted as False even though it is not None
    pat_evar = EVar.deconstruct(pattern)
    inst_evar = EVar.deconstruct(instance)
    if (pat_evar is not None) and (inst_evar is not None):
        if pat_evar != inst_evar:
            return None
        return ret
    pat_svar = SVar.deconstruct(pattern)
    inst_svar = SVar.deconstruct(instance)
    if (pat_svar is not None) and (inst_svar is not None):
        if pat_svar != inst_svar:
            return None
        return ret
    pat_sym = Symbol.deconstruct(pattern)
    inst_sym = Symbol.deconstruct(instance)
    if (pat_sym is not None) and (inst_sym is not None):
        if pat_sym != inst_sym:
            return None
        return ret
    if (pat_app := App.unwrap(pattern)) and (inst_app := App.unwrap(instance)):
        ret = match_single(pat_app[0], inst_app[0], ret)
        if ret is None:
            return None
        return match_single(pat_app[1], inst_app[1], ret)
    if (pat_ex := Exists.deconstruct(pattern)) and (inst_ex := Exists.deconstruct(instance)):
        if pat_ex[0] != inst_ex[0]:
            return None
        return match_single(pat_ex[1], inst_ex[1], ret)
    if (pat_mu := Mu.deconstruct(pattern)) and (inst_mu := Mu.deconstruct(instance)):
        if pat_mu[0] != inst_mu[0]:
            return None
        return match_single(pat_mu[1], inst_mu[1], ret)
    if (
        isinstance(pattern, ESubst)
        or isinstance(pattern, SSubst)
        or isinstance(instance, ESubst)
        or isinstance(instance, SSubst)
    ):
        raise NotImplementedError

    return None


def match(equations: list[tuple[Pattern, Pattern]]) -> dict[int, Pattern] | None:
    ret: dict[int, Pattern] = {}
    for pattern, instance in equations:
        submatch = match_single(pattern, instance, ret)
        if not submatch:
            return None
        ret = submatch
    return ret


"""
Pretty diffing
==============
"""


@dataclass(frozen=True)
class _Diff(Pattern):
    """
    To avoid re-implementing the pretty printing for diffs,
    we define a dummy subclass of Pattern.
    """

    """ Pattern to be printed with minuses in the diff. """
    expected: Pattern

    """ Pattern to be printed with pluses in the diff. """
    actual: Pattern

    def occurring_vars(self) -> set[EVar | SVar]:
        raise NotImplementedError

    def pretty(self, opts: PrettyOptions) -> str:
        return f'\n--- {self.expected.pretty(opts)}\n+++ {self.actual.pretty(opts)}\n'

    def instantiate(self, delta: Mapping[int, Pattern]) -> Pattern:
        raise NotImplementedError

    def apply_esubst(self, evar_id: int, plug: Pattern) -> Pattern:
        raise NotImplementedError

    def apply_ssubst(self, svar_id: int, plug: Pattern) -> Pattern:
        raise NotImplementedError


def diff_inst(inst1: InstantiationDict, inst2: InstantiationDict) -> InstantiationDict:
    ret = {}
    for k, v1 in inst1.items():
        if k in inst2:
            ret[k] = insert_diff(v1, inst2[k])
        else:
            # TODO: We've lost the metavar's constraints here.
            # Since we're only using this for pretty printing this is OK?
            ret[k] = insert_diff(v1, MetaVar(k))
    for k, v2 in inst2.items():
        if k in inst1:
            continue
        else:
            # TODO: We've lost the metavar's constraints here.
            ret[k] = insert_diff(MetaVar(k), v2)
    return frozendict(ret)


def insert_diff(p1: Pattern, p2: Pattern) -> Pattern:
    match (p1, p2):
        case (p1, p2) if p1 == p2:
            return p1
        case (App(l1, r1), App(l2, r2)):
            return App(insert_diff(l1, l2), insert_diff(r1, r2))
        case (Implies(l1, r1), Implies(l2, r2)):
            return Implies(insert_diff(l1, l2), insert_diff(r1, r2))
        case (Exists(var1, sp1), Exists(var2, sp2)) if var1 == var2:
            return Exists(var1, insert_diff(sp1, sp2))
        case (Mu(var1, sp1), Mu(var2, sp2)) if var1 == var2:
            return Mu(var1, insert_diff(sp1, sp2))
        case (Instantiate(sp1, inst1), Instantiate(sp2, inst2)) if sp1 == sp2:
            return Instantiate(sp1, diff_inst(inst1, inst2))
        case (Instantiate(sp1, inst1), _):
            if inst2_ := match_single(sp1, p2):
                return insert_diff(Instantiate(sp1, inst1), Instantiate(sp1, frozendict(inst2_)))
            else:
                # Don't try matching in this case, because we lose readability.
                # In any case, the diff must occur pretty soon since the instantiate does not match.
                return _Diff(p1, p2)
        case (_, Instantiate(sp2, inst2)):
            if inst1_ := match_single(sp2, p1):
                return insert_diff(Instantiate(sp2, frozendict(inst1_)), Instantiate(sp2, inst2))
            else:
                # Don't try matching in this case, because we lose readability.
                # In any case, the diff must occur pretty soon since the instantiate does not match.
                return _Diff(p1, p2)
        case (p1, p2):  # if p1 != p2
            return _Diff(p1, p2)
    raise AssertionError


def pretty_diff(p1: Pattern, p2: Pattern, opts: PrettyOptions) -> str:
    return insert_diff(p1, p2).pretty(opts)
