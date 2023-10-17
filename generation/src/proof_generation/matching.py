from __future__ import annotations

from typing import TYPE_CHECKING

from proof_generation.pattern import Application, EVar, Exists, Implication, MetaVar, Mu, SVar, Symbol

if TYPE_CHECKING:
    from proof_generation.pattern import Pattern


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
    elif (pat_evar := EVar.unwrap(pattern)) and (inst_evar := EVar.unwrap(instance)):
        if pat_evar != inst_evar:
            return None
    elif (pat_svar := SVar.unwrap(pattern)) and (inst_svar := SVar.unwrap(instance)):
        if pat_svar != inst_svar:
            return None
    elif (pat_sym := Symbol.unwrap(pattern)) and (inst_sym := Symbol.unwrap(instance)):
        if pat_sym != inst_sym:
            return None
    elif (pat_imp := Implication.unwrap(pattern)) and (inst_imp := Implication.unwrap(instance)):
        ret = match_single(pat_imp[0], inst_imp[0], ret)
        if not ret:
            return None
        ret = match_single(pat_imp[1], inst_imp[1], ret)
    elif (pat_app := Application.unwrap(pattern)) and (inst_app := Application.unwrap(instance)):
        ret = match_single(pat_app[0], inst_app[0], ret)
        if not ret:
            return None
        ret = match_single(pat_app[1], inst_app[1], ret)
    elif (pat_ex := Exists.unwrap(pattern)) and (inst_ex := Exists.unwrap(instance)):
        if pat_ex[0] != inst_ex[0]:
            return None
        ret = match_single(pat_ex[1], inst_ex[1], ret)
    elif (pat_mu := Mu.unwrap(pattern)) and (inst_mu := Mu.unwrap(instance)):
        if pat_mu[0] != inst_mu[0]:
            return None
        ret = match_single(pat_mu[1], inst_mu[1], ret)
    # TODO Consider adding cases for ESubst/SSubst
    else:
        return None
    return ret


def match(equations: list[tuple[Pattern, Pattern]]) -> dict[int, Pattern] | None:
    ret: dict[int, Pattern] = {}
    for pattern, instance in equations:
        submatch = match_single(pattern, instance, ret)
        if not submatch:
            return None
        ret = submatch
    return ret
