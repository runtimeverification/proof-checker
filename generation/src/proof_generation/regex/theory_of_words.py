from __future__ import annotations

from typing import TYPE_CHECKING

from ..pattern import MetaVar, Mu, Notation, SVar, Symbol, _or
from ..proofs.kore import nary_app
from ..proofs.propositional import Propositional

if TYPE_CHECKING:
    from typing import Final

    from ..proof import ProofThunk


class Words(Propositional):
    def __init__(self):
        super().__init__()
        self.add_notations([self.notations.eps, self.notations.a, self.notations.b, self.notations.concat])
        ten_nodes = (self.notations.accepting_node(i) for i in range(0, 10))
        self.add_notations(ten_nodes)

    class _Notations:
        eps: Final = Notation('epsilon', 0, Symbol('eps'), 'epsilon')
        a: Final = Notation('a', 0, Symbol('a'), 'a')
        b: Final = Notation('b', 0, Symbol('b'), 'b')
        concat: Final = nary_app(Symbol('concat'), 2, '[{0} {1}]')
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

    def accepting_has_ewp(self, binder: int) -> ProofThunk:
        """
        An accepting node contains the empty word.

        Words |-  epsilon ->  accepting(binder, _, _)
        """

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
        (accepting_node(_, l, r) . top_letter) -> accepting_node(_, l, r)
        -----------------------------------------------------------------
                            accepting_node(_, l, r)
        """

    def total_dfa_is_valid_base(self) -> ProofThunk:
        """
        Here, contextual implication `-o` binds box.

        Words |- (box . top_letter -o phi) . top_letter -> phi
        """

    def total_dfa_is_valid_recursive(
        self,
        binder: int,
        a_has_ewp: ProofThunk,
        b_has_ewp: ProofThunk,
        a_recurse: ProofThunk,
        b_recurse: ProofThunk,
    ) -> ProofThunk:
        """
           a_has_ewp: epsilon -> s[ accepting(fp_unf_a, fp_unf_b) / X ] fp_unf_a
           b_has_ewp: epsilon -> s[ accepting(fp_unf_a, fp_unf_b) / X ] fp_unf_b
           a_recurse: (SSubst[ (ctximp_app box (sVar box . top_letter) accepting(fp_unf_a, fp_unf_b) / X ] fp_ctximp_a) . top_letter) -> SSubst[ accepting(fp_unf_a, fp_unf_b) / X ] fp_unf_a$
           b_recurse: (SSubst[ (ctximp_app box (sVar box . top_letter) accepting(fp_unf_a, fp_unf_b) / X ] fp_ctximp_b) . top_letter) -> SSubst[ accepting(fp_unf_a, fp_unf_b) / X ] fp_unf_b$
           ------------------------
        `  accepting(fp_ctximp_a, fp_ctximp_b) . top_letter -> accepting(fp_unf_a, fp_unf_b)
        """
