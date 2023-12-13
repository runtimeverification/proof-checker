from __future__ import annotations

from typing import TYPE_CHECKING

import pytest

from proof_generation.interpreter import ExecutionPhase
from proof_generation.pattern import PrettyOptions, SVar
from proof_generation.proof import Claim
from proof_generation.regex.brzozowski import (
    FixpointPatternInstr,
    brzozowski,
    derivative,
    ml_accepting_node,
    null_instr,
)
from proof_generation.regex.regex import Choice, Concat, Epsilon, Kleene, Not, a, b, implies
from proof_generation.regex.theory_of_words import Words
from proof_generation.stateful_interpreter import StatefulInterpreter

if TYPE_CHECKING:
    from proof_generation.pattern import Pattern
    from proof_generation.regex.regex import Regex

even = Kleene(Choice(Concat(a, a), Choice(Concat(a, b), Choice(Concat(b, a), Concat(b, b)))))
odd = Concat(Choice(a, b), even)
top = Kleene(Choice(a, b))


def test_derivative() -> None:
    assert odd == derivative(a, even)


def brz(exp: Regex) -> bool:
    return brzozowski(exp, null_instr)


a_star_star_implies_a_star = implies(Kleene(Kleene(a)), Kleene(a))
a_star_star_implies_a_star_star = implies(Kleene(Kleene(a)), Kleene(Kleene(a)))
example_on_paper = implies(Kleene(Concat(a, a)), Choice(Concat(Kleene(a), a), Epsilon()))
asb_star_or_bsa_star = Choice(Kleene(Concat(Kleene(a), b)), Kleene(Concat(Kleene(b), a)))
even_or_odd = Choice(even, odd)
no_contains_a_or_no_only_b = Choice(Not(Concat(top, Concat(a, top))), Not(Kleene(b)))


def test_brzozowski() -> None:
    assert brz(a) == False
    assert brz(b) == False
    assert brz(Choice(a, b)) == False
    assert brz(top) == True
    assert brz(a_star_star_implies_a_star) == True
    assert brz(a_star_star_implies_a_star_star) == True
    assert brz(example_on_paper) == True
    assert brz(asb_star_or_bsa_star) == True
    assert brz(even) == False
    assert brz(even_or_odd) == True
    assert brz(no_contains_a_or_no_only_b)


acc = ml_accepting_node

# fmt: off
@pytest.mark.parametrize('exp,expected',
    # Regex                                 # pat(Q) for regex
    [ (top,                                 acc(0)(SVar(0), SVar(0))),

      (a_star_star_implies_a_star,          acc(0)(acc(1)(acc(2)(SVar(2), acc(3)(SVar(3), SVar(3))),
                                                          acc(2)(SVar(2), SVar(2))),
                                                   acc(1)(SVar(1), SVar(1)))),

      (a_star_star_implies_a_star_star,     acc(0)(acc(1)(acc(2)(acc(3)(SVar(3), acc(4)(SVar(4), SVar(4))),
                                                                 acc(3)(SVar(3), SVar(3))),
                                                     acc(2)(SVar(2), SVar(2))),
                                                   acc(1)(SVar(1), SVar(1)))),

      (example_on_paper,                    acc(0)(acc(1)(acc(2)(acc(3)(SVar(2),
                                                                        acc(4)(SVar(4), SVar(4))),
                                                                 acc(3)(SVar(3), SVar(3))),
                                                          acc(2)(SVar(2), SVar(2))),
                                                   acc(1)(SVar(1), SVar(1)))),
    ]
)
# fmt: on
def test_fixpoint_pattern(exp: Regex, expected: Pattern) -> None:
    words = Words()
    pretty_opts = words.pretty_options()

    instr = FixpointPatternInstr()
    assert brzozowski(exp, instr) == True
    assert instr.pattern
    assert instr.pattern.pretty(pretty_opts) == expected.pretty(pretty_opts)
    assert instr.pattern == expected


def test_theory_of_words() -> None:
    words = Words()
    claims = [Claim(claim) for claim in words.get_claims()]
    interpreter = StatefulInterpreter(ExecutionPhase.Gamma, claims=claims)
    words.execute_full(interpreter)
    assert interpreter.claims == []
