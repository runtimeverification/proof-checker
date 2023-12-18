from __future__ import annotations

from typing import TYPE_CHECKING

from .syntax import App, EVar, Exists, Implies, MetaVar, Mu, Pattern, SVar, Symbol

if TYPE_CHECKING:
    pass


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
    # TODO Consider adding cases for ESubst/SSubst
    return None


def match(equations: list[tuple[Pattern, Pattern]]) -> dict[int, Pattern] | None:
    ret: dict[int, Pattern] = {}
    for pattern, instance in equations:
        submatch = match_single(pattern, instance, ret)
        if not submatch:
            return None
        ret = submatch
    return ret
