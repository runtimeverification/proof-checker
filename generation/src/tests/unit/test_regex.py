import pytest
from dataclasses import dataclass, field
from proof_generation.regex.regex import Regex, Kleene, Choice, Concat, implies, Letter, a, b, EmptySet, Epsilon, Not, less_than
from proof_generation.regex.brzozowski import derivative, brzozowski, null_instr, BrzInstumentation
from proof_generation.pattern import Pattern, Implies, MetaVar, _and, _or, bot, equiv, neg, phi0, phi1, phi2, top, Notation, Symbol, SVar, Mu, PrettyOptions
from proof_generation.proofs.kore import nary_app

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


ml_eps = Notation('epsilon', 0, Symbol('eps'), 'epsilon')
ml_a  = Notation('a', 0, Symbol('a'), 'a')
ml_b  = Notation('b', 0, Symbol('b'), 'b')
ml_concat = nary_app(Symbol('concat'), 2, '[{0} {1}]')

def ml_accepting_node(node_id: int) -> Notation:
    return Notation('accepting', 2,
                    Mu(node_id, _or(ml_eps(), _or(ml_concat(ml_a(), MetaVar(0)), ml_concat(ml_b(), MetaVar(1))))),
                    f'accepting({node_id}, {{0}}, {{1}})')

@dataclass
class FixpointPatternInstr(BrzInstumentation):
    """ Partially computed fixpoint patterns.

        None indicates the a-node's pattern has not been computed,
        A Pattern indicates that we have finished computing the a-node's pattern
        and are now constructing the b-node's pattern.
    """
    stack : list[None | Pattern] = field(default_factory=lambda: [])
    pattern : None | Pattern = None

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
            b_pat = p
            self.node_completed(ml_accepting_node(len(self.stack))(a_pat, b_pat))

acc = ml_accepting_node
ten_nodes = (acc(i) for i in range(0, 10))
pretty_options = PrettyOptions(notations={n.definition: n for n in ten_nodes}, simplify_instantiations=False)

@pytest.mark.parametrize('exp,expected',
    [ (top, acc(0)(SVar(0), SVar(0))),
      (a_star_star_implies_a_star, acc(0)(acc(1)(acc(2)(SVar(2), acc(3)(SVar(3), SVar(3))),
                                                 acc(2)(SVar(2), SVar(2))),
                                          acc(1)(SVar(1), SVar(1)))),
      (a_star_star_implies_a_star_star, acc(0)(acc(1)(acc(2)(acc(3)(SVar(3), acc(4)(SVar(4), SVar(4))), acc(3)(SVar(3), SVar(3))),
                                                 acc(2)(SVar(2), SVar(2))),
                                          acc(1)(SVar(1), SVar(1)))),
      (example_on_paper, acc(0)(acc(1)(acc(2)(acc(3)(SVar(2),
                                                     acc(4)(SVar(4), SVar(4))),
                                              acc(3)(SVar(3), SVar(3))),
                                       acc(2)(SVar(2), SVar(2))),
                                acc(1)(SVar(1), SVar(1)))),
    ]
)
def test_fixpoint_pattern(exp: Regex, expected: Pattern) -> None:
    instr = FixpointPatternInstr()
    assert brzozowski(exp, instr) == True
    assert instr.pattern.pretty(pretty_options) == expected.pretty(pretty_options)
    assert instr.pattern == expected
