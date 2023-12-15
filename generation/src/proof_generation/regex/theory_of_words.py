from __future__ import annotations

from typing import TYPE_CHECKING

from ..aml import EVar, Exists, Implies, MetaVar, Mu, Notation, SVar, Symbol, _or
from ..proof import ProofThunk
from ..proofs.definedness import subset
from ..proofs.kore import nary_app
from ..proofs.propositional import Propositional, _and, phi0, phi1
from ..proved import Proved

if TYPE_CHECKING:
    from typing import Final

    from ..aml import Pattern


class Words(Propositional):
    def __init__(self):
        super().__init__()
        self.add_notation(self.notations.ctximp(0))
        self.add_notations(
            [self.notations.eps, self.notations.a, self.notations.b, self.notations.concat, self.notations.top_letter]
        )
        ten_nodes = (self.notations.accepting_node(i) for i in range(0, 10))
        self.add_notations(ten_nodes)

    class _Notations:
        # TODO: Move to definedness
        definedness_symbol = Symbol('⌈_⌉')

        def ctximp(self, hole: int) -> Notation:
            return Notation(
                'ctximp', 2, Exists(hole, _and(EVar(hole), subset(phi0, phi1))), f'< {{0}} -o[{hole}] {{1}} >'
            )

        eps: Final = Notation('epsilon', 0, Symbol('eps'), 'epsilon')
        a: Final = Notation('a', 0, Symbol('a'), 'a')
        b: Final = Notation('b', 0, Symbol('b'), 'b')
        concat: Final = nary_app(Symbol('concat'), 2)
        top_letter = Notation('top_letter', 0, _or(a(), b()), 'top_letter')
        top_word = Notation('top_word', 0, Mu(0, _or(eps(), concat(top_letter(), SVar(0)))), 'top_word')

        def accepting_node(self, node_id: int) -> Notation:
            """Represents an accepting node in a DFA"""
            return Notation(
                'accepting',
                2,
                Mu(node_id, _or(self.eps(), _or(self.concat(self.a(), MetaVar(0)), self.concat(self.b(), MetaVar(1))))),
                f'accepting({node_id}, {{0}}, {{1}})',
            )

    notations = _Notations()

    """
    General Lemmas
    --------------
    """

    def accepting_has_ewp(self, binder: int, accepting: Pattern) -> ProofThunk:
        """
        An accepting node contains the empty word.

        Words |-  epsilon ->  accepting(binder, left_child, right_child)
        """

        self.notations.accepting_node(binder).assert_matches(accepting)

        return ProofThunk(
            lambda _: Proved(Implies(self.notations.eps(), accepting)),
            Implies(self.notations.eps(), accepting),
        )

    """
    Proving (the ML representation of) the language of a DFA is total
    -----------------------------------------------------------------

    We want to prove that a pattern of a DFA where all nodes are accepting
    is valid. This pattern will be a nested instantiation of the `accepting_node`
    notation, and the set variables bound by them.

    Let `pat(Q)` be the ML-representation of the language of a total DFA.
    and `pat(n)` the subpattern correspnding to the node `n`.
    We want to prove: `Words |- pat(Q)`.
    We break this up into the following steps:

    1.  First we reduce this to `Words |- top_word -> pat(Q)`,
        and then to `Words |- pat(Q) . top_letter -> pat(Q)`.
        This is encapsulated in `total_dfa_is_valid_init`.

    2.  The hypothesis for the above is proved inductivly.
        In the recursive cases, we apply KT and reduce those to the subcases
        using framing. Note the different substitutions involved on the LHS and RHS.
        See paper for full details.
    """

    def total_dfa_is_valid_init(self, binder: int, hypothesis: ProofThunk) -> ProofThunk:
        """
        (accepting_node(binder, l, r) . top_letter) -> accepting_node(binder, l, r)
        -----------------------------------------------------------------
                            accepting_node(binder, l, r)
        """

        n = self.notations

        lhs, rhs = Implies.extract(hypothesis.conc)
        n.accepting_node(binder).assert_matches(rhs)
        concat_left, concat_right = n.concat.assert_matches(lhs)
        assert concat_left == rhs, self.pretty_diff(concat_left, rhs)
        assert concat_right == n.top_letter(), self.pretty_diff(rhs, n.top_letter())

        return ProofThunk(lambda _: Proved(rhs), rhs)

    def total_dfa_is_valid_base(self, phi: Pattern) -> ProofThunk:
        """
        Here, contextual implication `-o` binds box.

        Words |- (box . top_letter -o phi) . top_letter -> phi
        """
        return ProofThunk(
            lambda _: Proved(
                Implies(
                    self.notations.concat(
                        self.notations.ctximp(0)(self.notations.concat(EVar(0), self.notations.top_letter()), phi),
                        self.notations.top_letter(),
                    ),
                    phi,
                )
            ),
            Implies(
                self.notations.concat(
                    self.notations.ctximp(0)(self.notations.concat(EVar(0), self.notations.top_letter()), phi),
                    self.notations.top_letter(),
                ),
                phi,
            ),
        )

    def total_dfa_is_valid_recursive(
        self,
        binder: int,
        fp_unf_a: Pattern,
        fp_unf_b: Pattern,
        fp_ctximp_a: Pattern,
        fp_ctximp_b: Pattern,
        eps_in_a_unf: ProofThunk,
        eps_in_b_unf: ProofThunk,
        a_recurse: ProofThunk,
        b_recurse: ProofThunk,
    ) -> ProofThunk:
        """
        eps_in_a_unf: epsilon -> SSubst[ accepting(fp_unf_a, fp_unf_b) / binder ] fp_unf_a
        eps_in_b_unf: epsilon -> SSubst[ accepting(fp_unf_a, fp_unf_b) / binder ] fp_unf_b
        a_recurse: (SSubst[  (hole . top_letter) -o accepting(fp_unf_a, fp_unf_b) / binder ] fp_ctximp_a) . top_letter) -> SSubst[ accepting(fp_unf_a, fp_unf_b) / binder ] fp_unf_a$
        b_recurse: (SSubst[  (hole . top_letter) -o accepting(fp_unf_a, fp_unf_b) / binder ] fp_ctximp_b) . top_letter) -> SSubst[ accepting(fp_unf_a, fp_unf_b) / binder ] fp_unf_b$
        ------------------------
        accepting(fp_ctximp_a, fp_ctximp_b) . top_letter -> accepting(fp_unf_a, fp_unf_b)
        """

        n = self.notations

        unfolded_node = n.accepting_node(binder)(fp_unf_a, fp_unf_b)  # accepting(binder, fp_unf_a, fp_unf_b)
        indhyp_pat = n.ctximp(0)(
            n.concat(EVar(0), n.top_letter()), unfolded_node
        )  # (hole . top_letter) -o unfolded_node

        rhs_a = fp_unf_a.apply_ssubst(binder, unfolded_node)
        rhs_b = fp_unf_b.apply_ssubst(binder, unfolded_node)

        assert eps_in_a_unf.conc == Implies(n.eps(), rhs_a)
        assert eps_in_b_unf.conc == Implies(n.eps(), rhs_b)
        assert a_recurse.conc == Implies(n.concat(fp_ctximp_a.apply_ssubst(binder, indhyp_pat), n.top_letter()), rhs_a)
        assert b_recurse.conc == Implies(n.concat(fp_ctximp_b.apply_ssubst(binder, indhyp_pat), n.top_letter()), rhs_b)
        return ProofThunk(
            lambda _: Proved(
                Implies(
                    n.concat(n.accepting_node(binder)(fp_ctximp_a, fp_ctximp_b), n.top_letter()),
                    n.accepting_node(binder)(fp_unf_a, fp_unf_b),
                )
            ),
            Implies(
                n.concat(n.accepting_node(binder)(fp_ctximp_a, fp_ctximp_b), n.top_letter()),
                n.accepting_node(binder)(fp_unf_a, fp_unf_b),
            ),
        )
