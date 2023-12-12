from __future__ import annotations

from dataclasses import dataclass, field
from typing import TYPE_CHECKING

from proof_generation.pattern import MetaVar, Mu, Notation, SVar, Symbol, _or
from proof_generation.proofs.kore import nary_app

from .regex import Choice, Concat, EmptySet, Epsilon, Kleene, Letter, Not, a, b, less_than

if TYPE_CHECKING:
    from proof_generation.pattern import Pattern

    from .regex import Regex


def has_ewp(exp: Regex) -> bool:
    match exp:
        case EmptySet():
            return False
        case Epsilon():
            return True
        case Letter(_):
            return False
        case Concat(l, r):
            return has_ewp(l) and has_ewp(r)
        case Choice(l, r):
            return has_ewp(l) or has_ewp(r)
        case Kleene(_):
            return True
        case Not(e):
            return not has_ewp(e)
        case _:
            raise AssertionError(exp)


def left_assoc(exp: Regex) -> Regex:
    match exp:
        case Concat(Concat(e1, e2), e3):
            return left_assoc(Concat(e1, Concat(e2, e3)))
        case Concat(e1, e2):
            return Concat(e1, left_assoc(e2))

        case Choice(Choice(e1, e2), e3):
            return left_assoc(Choice(e1, Choice(e2, e3)))
        case Choice(e1, e2):
            return Choice(e1, left_assoc(e2))

        case Kleene(e):
            return Kleene(left_assoc(e))
        case Not(e):
            return Not(left_assoc(e))

        case _:
            return exp


def identities(exp: Regex) -> Regex:
    match exp:
        case Concat(EmptySet(), e2):
            return EmptySet()
        case Concat(e1, EmptySet()):
            return EmptySet()
        case Concat(Epsilon(), e2):
            return e2
        case Concat(e1, Epsilon()):
            return e1
        case Concat(e1, e2):
            return Concat(identities(e1), identities(e2))

        case Choice(e1, EmptySet()):
            return identities(e1)
        case Choice(EmptySet(), e1):
            return identities(e1)
        case Choice(e1, Choice(e2, e3)) if e1 == e2:
            return Choice(e1, e3)
        case Choice(e1, e2) if e1 == e2:
            return e1
        case Choice(e1, e2):
            return Choice(identities(e1), identities(e2))

        case Kleene(Kleene(e)):
            return identities(Kleene(e))
        case Kleene(e):
            return Kleene(identities(e))

        case Not(e):
            return Not(identities(e))

        case _:
            return exp


def sort_choice(exp: Regex) -> Regex:
    match exp:
        case Concat(e1, e2):
            return Concat(sort_choice(e1), sort_choice(e2))
        case Choice(e1, Choice(e2, e3)):
            if less_than(e1, e2):
                return Choice(e1, sort_choice(Choice(e2, e3)))
            else:
                return Choice(e2, sort_choice(Choice(e1, e3)))
        case Kleene(e):
            return Kleene(sort_choice(e))
        case Not(e):
            return Not(sort_choice(e))
        case _:
            return exp


def normalize(exp: Regex) -> Regex:
    prev = None
    ret = exp
    while prev != ret:
        prev = ret
        ret = left_assoc(ret)
        ret = identities(ret)
        ret = sort_choice(ret)
    return ret


def derivative(by: Letter, exp: Regex) -> Regex:
    match exp:
        case EmptySet():
            return EmptySet()
        case Epsilon():
            return EmptySet()
        case Letter(n):
            if n == by.name:
                return Epsilon()
            else:
                return EmptySet()
        case Concat(l, r):
            if has_ewp(l):
                return normalize(Choice(Concat(derivative(by, l), r), derivative(by, r)))
            else:
                return normalize(Concat(derivative(by, l), r))
        case Choice(l, r):
            return normalize(Choice(derivative(by, l), derivative(by, r)))
        case Kleene(e):
            return normalize(Concat(derivative(by, e), Kleene(e)))
        case Not(e):
            return normalize(Not(derivative(by, e)))
        case _:
            raise AssertionError


class BrzInstumentation:
    def enter_node(self) -> None:
        pass

    def exit_node(self) -> None:
        pass

    def leaf(self, index: int) -> None:
        pass


null_instr = BrzInstumentation()


def brzozowski(exp: Regex, instr: BrzInstumentation, prev: list[Regex] | None = None) -> bool:
    if prev == None:
        prev = []
    assert prev is not None

    if exp in prev:
        instr.leaf(prev.index(exp))
        return True
    if not has_ewp(exp):
        return False

    prev.append(exp)
    instr.enter_node()

    left = brzozowski(derivative(a, exp), instr, prev=prev)
    right = brzozowski(derivative(b, exp), instr, prev=prev)

    prev.pop()
    instr.exit_node()
    return left and right


# Proof Generation
# ================

ml_eps = Notation('epsilon', 0, Symbol('eps'), 'epsilon')
ml_a = Notation('a', 0, Symbol('a'), 'a')
ml_b = Notation('b', 0, Symbol('b'), 'b')
ml_concat = nary_app(Symbol('concat'), 2, '[{0} {1}]')


def ml_accepting_node(node_id: int) -> Notation:
    return Notation(
        'accepting',
        2,
        Mu(node_id, _or(ml_eps(), _or(ml_concat(ml_a(), MetaVar(0)), ml_concat(ml_b(), MetaVar(1))))),
        f'accepting({node_id}, {{0}}, {{1}})',
    )


@dataclass
class FixpointPatternInstr(BrzInstumentation):
    stack: list[None | Pattern] = field(default_factory=lambda: [])
    """Partially computed fixpoint patterns.

    None indicates the a-node's pattern has not been computed,
    A Pattern indicates that we have finished computing the a-node's pattern
    and are now constructing the b-node's pattern.
    """

    pattern: None | Pattern = None

    def enter_node(self) -> None:
        self.stack.append(None)

    def exit_node(self) -> None:
        pass

    def leaf(self, index: int) -> None:
        self.node_completed(SVar(index))

    def node_completed(self, p: Pattern) -> None:
        if not self.stack:
            assert self.pattern == None
            self.pattern = p
        elif self.stack[-1] == None:
            self.stack[-1] = p
        else:
            a_pat = self.stack.pop()
            assert a_pat
            b_pat = p
            self.node_completed(ml_accepting_node(len(self.stack))(a_pat, b_pat))
