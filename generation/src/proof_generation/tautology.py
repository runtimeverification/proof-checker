# NOTE that the resolution algorithm can be made more efficient by only computing
# a proof of implication rather than equivalence in some of the proof procedures.
# But we favoured a set of utility functions that can be used in other contexts as well.

from __future__ import annotations

from itertools import combinations
from typing import TYPE_CHECKING

from proof_generation.pattern import Implies, MetaVar, Notation, match_single, phi0, phi1, phi2
from proof_generation.proof import ProofExp
from proof_generation.proofs.propositional import And, Equiv, Negation, Or, Propositional, _build_subst, bot, neg, top

if TYPE_CHECKING:
    from collections.abc import Callable

    from proof_generation.basic_interpreter import BasicInterpreter
    from proof_generation.pattern import Pattern
    from proof_generation.proof import ProofThunk

### Helper types ###

# The following represents a right-associated disjunction of
# metavariables with the id's in the list. Negative id's represent
# negated metavars. The disjunction is not Bottom terminated.
Clause = list[int]

# Conjunction of right-associated clauses, not Top terminated
ClauseConjunction = list[Clause]


# Structure of Conjunctive Form Tree
class ConjForm:
    negated: bool

    def __init__(self, negated: bool):
        self.negated = negated

    def __str__(self) -> str:
        return str(conj_to_pattern(self))


class CFAnd(ConjForm):
    left: ConjForm
    right: ConjForm

    def __init__(self, left: ConjForm, right: ConjForm):
        super().__init__(False)
        self.left = left
        self.right = right


class CFOr(ConjForm):
    left: ConjForm
    right: ConjForm

    def __init__(self, left: ConjForm, right: ConjForm):
        super().__init__(False)
        self.left = left
        self.right = right


class CFBot(ConjForm):
    pass


class CFVar(ConjForm):
    id: int

    def __init__(self, id: int):
        super().__init__(False)
        self.id = id


def conj_to_pattern(term: ConjForm) -> Pattern:
    pat: Pattern
    if isinstance(term, CFBot):
        pat = bot
    elif isinstance(term, CFVar):
        pat = MetaVar(term.id)
    elif isinstance(term, CFOr):
        pat = Or(conj_to_pattern(term.left), conj_to_pattern(term.right))
    elif isinstance(term, CFAnd):
        pat = And(conj_to_pattern(term.left), conj_to_pattern(term.right))
    if term.negated:
        pat = neg(pat)
    return pat


def id_to_metavar(id: int) -> Pattern:
    assert id != 0
    if id < 0:
        return neg(MetaVar(-(id + 1)))
    return MetaVar(id - 1)


def foldl_op(op: Callable[[Pattern, Pattern], Pattern], l: list[Pattern], start: int = 0, end: int = -1) -> Pattern:
    if end < 0:
        end = end + len(l)
    if start < end:
        return op(foldl_op(op, l, start, end - 1), l[end])
    return l[start]


def foldr_op(op: Callable[[Pattern, Pattern], Pattern], l: list[Pattern], start: int = 0, end: int = -1) -> Pattern:
    if end < 0:
        end = end + len(l)
    if start < end:
        return op(l[start], foldr_op(op, l, start + 1, end))
    return l[start]


def clause_to_pattern(l: list[int]) -> Pattern:
    if not l:
        return bot
    return foldr_op(Or, [id_to_metavar(id) for id in l])


def clause_list_to_pattern(l: list[list[int]]) -> Pattern:
    if not l:
        return top
    return foldr_op(And, [clause_to_pattern(cl) for cl in l])


class ResolutionHintSource:
    left_set: frozenset[int]
    right_set: frozenset[int]
    resolvant: int

    def __init__(self, left_set: frozenset[int], right_set: frozenset[int], resolvant: int) -> None:
        self.left_set = left_set
        self.right_set = right_set
        self.resolvant = resolvant


ResolutionHint = dict[frozenset[int], ResolutionHintSource | int]


class Tautology(ProofExp):
    prop: Propositional

    def __init__(self, interpreter: BasicInterpreter) -> None:
        super().__init__(interpreter)
        self.prop = Propositional(interpreter)

    @staticmethod
    def claims() -> list[Pattern]:
        return []

    @staticmethod
    def axioms() -> list[Pattern]:
        return [
            Implies(And(And(phi0, phi1), phi2), And(phi0, And(phi1, phi2))),
            Implies(And(phi0, And(phi1, phi2)), And(And(phi0, phi1), phi2)),
            Implies(Or(Or(phi0, phi1), phi2), Or(phi0, Or(phi1, phi2))),
            Implies(Or(phi0, Or(phi1, phi2)), Or(Or(phi0, phi1), phi2)),
            Implies(Or(And(phi0, phi1), phi2), And(Or(phi0, phi2), Or(phi1, phi2))),
            Implies(And(Or(phi0, phi2), Or(phi1, phi2)), Or(And(phi0, phi1), phi2)),
            Implies(Or(phi0, And(phi1, phi2)), And(Or(phi0, phi1), Or(phi0, phi2))),
            Implies(And(Or(phi0, phi1), Or(phi0, phi2)), Or(phi0, And(phi1, phi2))),
        ]

    def imp_trans_match1(self, h1: ProofThunk, h2: ProofThunk) -> ProofThunk:
        """Same as imp_transitivity but h1 is instantiated to match h2"""
        _, b = Implies.extract(h1.conc)
        c, _ = Implies.extract(h2.conc)
        subst = match_single(b, c, {})
        assert subst is not None
        actual_subst: dict[int, Pattern] = subst
        return self.prop.imp_transitivity(self.dynamic_inst(h1, actual_subst), h2)

    def imp_trans_match2(self, h1: ProofThunk, h2: ProofThunk) -> ProofThunk:
        """Same as imp_transitivity but h2 is instantiated to match h1"""
        _, b = Implies.extract(h1.conc)
        c, _ = Implies.extract(h2.conc)
        subst = match_single(c, b, {})
        assert subst is not None
        actual_subst: dict[int, Pattern] = subst
        return self.prop.imp_transitivity(h1, self.dynamic_inst(h2, actual_subst))

    def and_assoc_r(self, pat1: Pattern = phi0, pat2: Pattern = phi1, pat3: Pattern = phi2) -> ProofThunk:
        """(a /\\ b) /\\ c -> a /\\ (b /\\ c)"""
        return self.dynamic_inst(self.load_axiom_by_index(0), _build_subst([pat1, pat2, pat3]))

    def and_assoc_l(self, pat1: Pattern = phi0, pat2: Pattern = phi1, pat3: Pattern = phi2) -> ProofThunk:
        """a /\\ (b /\\ c) -> (a /\\ b) /\\ c"""
        return self.dynamic_inst(self.load_axiom_by_index(1), _build_subst([pat1, pat2, pat3]))

    def or_assoc_r(self, pat1: Pattern = phi0, pat2: Pattern = phi1, pat3: Pattern = phi2) -> ProofThunk:
        """(a \\/ b) \\/ c -> a \\/ (b \\/ c)"""
        return self.dynamic_inst(self.load_axiom_by_index(2), _build_subst([pat1, pat2, pat3]))

    def or_assoc_l(self, pat1: Pattern = phi0, pat2: Pattern = phi1, pat3: Pattern = phi2) -> ProofThunk:
        """a \\/ (b \\/ c) -> (a \\/ b) \\/ c"""
        return self.dynamic_inst(self.load_axiom_by_index(3), _build_subst([pat1, pat2, pat3]))

    def or_distr_r(self, pat1: Pattern = phi0, pat2: Pattern = phi1, pat3: Pattern = phi2) -> ProofThunk:
        """(a /\\ b) \\/ c -> (a \\/ c) /\\ (b \\/ c)"""
        return self.dynamic_inst(self.load_axiom_by_index(4), _build_subst([pat1, pat2, pat3]))

    def or_distr_r_rev(self, pat1: Pattern = phi0, pat2: Pattern = phi1, pat3: Pattern = phi2) -> ProofThunk:
        """(a \\/ c) /\\ (b \\/ c) -> (a /\\ b) \\/ c"""
        return self.dynamic_inst(self.load_axiom_by_index(5), _build_subst([pat1, pat2, pat3]))

    def or_distr_l(self, pat1: Pattern = phi0, pat2: Pattern = phi1, pat3: Pattern = phi2) -> ProofThunk:
        """a \\/ (b /\\ c) -> (a \\/ b) /\\ (a \\/ c)"""
        return self.dynamic_inst(self.load_axiom_by_index(6), _build_subst([pat1, pat2, pat3]))

    def or_distr_l_rev(self, pat1: Pattern = phi0, pat2: Pattern = phi1, pat3: Pattern = phi2) -> ProofThunk:
        """(a \\/ b) /\\ (a \\/ c) -> a \\/ (b /\\ c)"""
        return self.dynamic_inst(self.load_axiom_by_index(7), _build_subst([pat1, pat2, pat3]))

    def and_assoc(self, pat1: Pattern = phi0, pat2: Pattern = phi1, pat3: Pattern = phi2) -> ProofThunk:
        """a /\\ (b /\\ c) <-> (a /\\ b) /\\ c"""
        return self.prop.and_intro(self.and_assoc_l(pat1, pat2, pat3), self.and_assoc_r(pat1, pat2, pat3))

    def or_assoc(self, pat1: Pattern = phi0, pat2: Pattern = phi1, pat3: Pattern = phi2) -> ProofThunk:
        """a \\/ (b \\/ c) <-> (a \\/ b) \\/ c"""
        return self.prop.and_intro(self.or_assoc_l(pat1, pat2, pat3), self.or_assoc_r(pat1, pat2, pat3))

    def and_comm_imp(self, p: Pattern = phi0, q: Pattern = phi1) -> ProofThunk:
        """p /\\ q -> q /\\ p"""
        return self.prop.con3_i(self.prop.con2(q, p))

    def and_comm(self, p: Pattern = phi0, q: Pattern = phi1) -> ProofThunk:
        """p /\\ q <-> q /\\ p"""
        return self.prop.and_intro(self.and_comm_imp(p, q), self.and_comm_imp(q, p))

    def or_comm_imp(self, p: Pattern = phi0, q: Pattern = phi1) -> ProofThunk:
        """p \\/ q -> q \\/ p"""
        return self.prop.imp_transitivity(self.prop.imp_trans(neg(p), q, bot), self.prop.dne_r(neg(q), p))

    def or_comm(self, p: Pattern = phi0, q: Pattern = phi1) -> ProofThunk:
        """p \\/ q <-> q \\/ p"""
        return self.prop.and_intro(self.or_comm_imp(p, q), self.or_comm_imp(q, p))

    def or_l_imp(self, p: Pattern, q: Pattern) -> ProofThunk:
        """p -> p \\/ q"""
        return self.ant_commutativity(self.absurd(p, q))

    def or_r_imp(self, p: Pattern, q: Pattern) -> ProofThunk:
        """q -> p \\/ q"""
        return self.p1(q, neg(p))

    def or_l(self, p_pf: ProofThunk, q: Pattern) -> ProofThunk:
        """
             p
        ------------
          p \\/ q
        """
        return self.mp(self.or_l_imp(p_pf.conc, q), p_pf)

    def or_r(self, q_pf: ProofThunk, p: Pattern) -> ProofThunk:
        """
             q
        ------------
          p \\/ q
        """
        return self.mp(self.or_r_imp(p, q_pf.conc), q_pf)

    def equiv_refl(self, p: Pattern = phi0) -> ProofThunk:
        """p <-> p"""
        pf = self.prop.imp_refl(p)
        return self.prop.and_intro(pf, pf)

    def equiv_sym(self, pf: ProofThunk) -> ProofThunk:
        """
          p <-> q
        -----------
          q <-> p
        """
        return self.prop.and_intro(self.prop.and_r(pf), self.prop.and_l(pf))

    def equiv_transitivity(self, pq_pf: ProofThunk, qr_pf: ProofThunk) -> ProofThunk:
        """
           p <-> q    q <-> r
        ----------------------
                p <-> r
        """
        return self.prop.and_intro(
            self.prop.imp_transitivity(self.prop.and_l(pq_pf), self.prop.and_l(qr_pf)),
            self.prop.imp_transitivity(self.prop.and_r(qr_pf), self.prop.and_r(pq_pf)),
        )

    def equiv_match_l(self, h: ProofThunk, p: Pattern) -> ProofThunk:
        a, b = Equiv.extract(h.conc)
        subst = match_single(a, p, {})
        assert subst is not None
        actual_subst: dict[int, Pattern] = subst
        return self.dynamic_inst(h, actual_subst)

    def equiv_match_r(self, h: ProofThunk, p: Pattern) -> ProofThunk:
        a, b = Equiv.extract(h.conc)
        subst = match_single(b, p, {})
        assert subst is not None
        actual_subst: dict[int, Pattern] = subst
        return self.dynamic_inst(h, actual_subst)

    def equiv_trans_match1(self, h1: ProofThunk, h2: ProofThunk) -> ProofThunk:
        """Same as equiv_transitivity but h1 is instantiated to match h2"""
        _, b = Equiv.extract(h1.conc)
        c, _ = Equiv.extract(h2.conc)
        subst = match_single(b, c, {})
        assert subst is not None
        actual_subst: dict[int, Pattern] = subst
        return self.equiv_transitivity(self.prop.dynamic_inst(h1, actual_subst), h2)

    def equiv_trans_match2(self, h1: ProofThunk, h2: ProofThunk) -> ProofThunk:
        """Same as equiv_transitivity but h2 is instantiated to match h1"""
        _, b = Equiv.extract(h1.conc)
        c, _ = Equiv.extract(h2.conc)
        subst = match_single(c, b, {})
        assert subst is not None
        actual_subst: dict[int, Pattern] = subst
        return self.equiv_transitivity(
            h1,
            self.prop.dynamic_inst(h2, actual_subst),
        )

    def and_cong(self, pf1: ProofThunk, pf2: ProofThunk) -> ProofThunk:
        return self.prop.and_intro(
            self.prop.imim_and(self.prop.and_l(pf1), self.prop.and_l(pf2)),
            self.prop.imim_and(self.prop.and_r(pf1), self.prop.and_r(pf2)),
        )

    def or_cong(self, pf1: ProofThunk, pf2: ProofThunk) -> ProofThunk:
        return self.prop.and_intro(
            self.prop.imim_or(self.prop.and_l(pf1), self.prop.and_l(pf2)),
            self.prop.imim_or(self.prop.and_r(pf1), self.prop.and_r(pf2)),
        )

    def resolution(self, p: Pattern = phi0, a: Pattern = phi1, b: Pattern = phi2) -> ProofThunk:
        """~p \\/ a -> p \\/ b -> a \\/ b"""
        return self.prop.imp_transitivity(self.or_comm_imp(neg(p), a), self.prop.imp_trans(neg(a), neg(p), b))

    def resolution_r(self, p: Pattern = phi0, b: Pattern = phi1) -> ProofThunk:
        """~p -> p \\/ b -> b"""
        return self.prop.ant_commutativity(self.prop.imp_refl(Or(p, b)))

    def resolution_l(self, p: Pattern = phi0, a: Pattern = phi1) -> ProofThunk:
        """~p \\/ a -> p -> a"""
        return self.prop.imim_l(a, self.prop.dneg_intro(p))

    def resolution_base(self, p: Pattern = phi0) -> ProofThunk:
        """~p -> p -> bot"""
        return self.prop.imp_refl(neg(p))

    def resolution_step(self, ab_pf: ProofThunk, ac_pf: ProofThunk, bcd_pf: ProofThunk) -> ProofThunk:
        """
          a -> b    a -> c    b -> c -> d
        -----------------------------------
                      a -> d
        """
        a, b = Implies.extract(ab_pf.conc)
        a2, c = Implies.extract(ac_pf.conc)
        assert a == a2
        b2, cd = Implies.extract(bcd_pf.conc)
        assert b == b2
        c2, d = Implies.extract(cd)
        assert c == c2
        return self.modus_ponens(
            self.modus_ponens(self.prop.prop2_inst(a, c, d), self.prop.imp_transitivity(ab_pf, bcd_pf)), ac_pf
        )

    def is_propositional(self, pat: Pattern) -> bool:
        if pat == bot:
            return True
        if pat_imp := Implies.unwrap(pat):
            return self.is_propositional(pat_imp[0]) and self.is_propositional(pat_imp[1])
        if isinstance(pat, MetaVar):
            return True
        if isinstance(pat, Notation):
            return self.is_propositional(pat.conclusion())
        return False

    # TODO Maybe refactor this code to only return a single ProofThunk
    # representing the conjunction of the two, but note that this may
    # come at a cost to performance, since you have to pack and unpack
    # conjunctions repeatedly
    def to_conj_form(self, pat: Pattern) -> tuple[ConjForm, ProofThunk, ProofThunk | None]:
        """
        Assumes the input is a propositional formula and transforms it to one
        made up of only ORs, negations and variables
        Output is:
          the representation of the new pattern
          proof that pat -> new pat
          proof that new pat -> pat
        NOTE! When the new term is Top or Bottom, we only populate the
        first proof; this proof will be a proof of `pat` or `neg(pat)`
        respectively (as opposed to, say, `pat -> Top``)
        """
        if pat == bot:
            return CFBot(False), self.prop.top_intro(), None
        if pat == top:
            return CFBot(True), self.prop.top_intro(), None
        if isinstance(pat, MetaVar):
            phi_imp_phi = self.prop.imp_refl(pat)
            return CFVar(pat.name), phi_imp_phi, phi_imp_phi
        elif pat_imp := Implies.extract(pat):
            pat0 = pat_imp[0]
            pat1 = pat_imp[1]
            pat1_conj, pat1_l, pat1_r = self.to_conj_form(pat1)

            if isinstance(pat1_conj, CFBot):
                if pat1_conj.negated:
                    pf = self.prop.imp_provable(pat0, pat1_l)
                    return CFBot(True), pf, None
                else:
                    pat0_conj, pat0_l, pat0_r = self.to_conj_form(pat0)
                    if isinstance(pat0_conj, CFBot):
                        if pat0_conj.negated:
                            pf = self.prop.and_not_r_intro(pat0_l, pat1_l)
                            return CFBot(False), pf, None
                        else:
                            pf = self.prop.absurd_i(pat0_l, pat1)
                            return CFBot(True), pf, None
                    if pat0_conj.negated:
                        pat0_conj.negated = False
                        assert pat0_r is not None
                        actual_pat0_r: ProofThunk = pat0_r
                        return (
                            pat0_conj,
                            self.prop.absurd3(actual_pat0_r, pat1_l),
                            self.prop.absurd4(pat0_l, pat1),
                        )
                    else:
                        pat0_conj.negated = True
                        assert pat0_r is not None
                        actual_pat0_r = pat0_r
                        return (
                            pat0_conj,
                            self.prop.imim(actual_pat0_r, pat1_l),
                            self.prop.absurd2(pat0_l, pat1),
                        )
            pat0_conj, pat0_l, pat0_r = self.to_conj_form(pat0)
            if isinstance(pat0_conj, CFBot):
                if pat0_conj.negated:
                    assert pat1_r is not None
                    actual_pat1_r: ProofThunk = pat1_r
                    return pat1_conj, self.prop.helper1(pat0_l, pat1_l), self.prop.a1d(actual_pat1_r, pat0)
                else:
                    pf = self.prop.absurd_i(pat0_l, pat1)
                    return CFBot(True), pf, None
            assert pat0_r is not None
            actual_pat0_r = pat0_r
            assert pat1_r is not None
            actual_pat1_r = pat1_r
            if pat0_conj.negated:
                pat0_conj.negated = False
                return (
                    CFOr(pat0_conj, pat1_conj),
                    self.prop.imim(actual_pat0_r, pat1_l),
                    self.prop.imim(pat0_l, actual_pat1_r),
                )
            else:
                pat0_conj.negated = True
                return (
                    CFOr(pat0_conj, pat1_conj),
                    self.prop.imim_nnr(actual_pat0_r, pat1_l),
                    self.prop.imim_nnl(pat0_l, actual_pat1_r),
                )
        else:
            raise AssertionError(f'Unexpected pattern! Expected a propositional pattern but got:\n{str(pat)}\n')

    def propag_neg(self, term: ConjForm) -> tuple[ConjForm, ProofThunk, ProofThunk]:
        """Assumes `term` is made up only of OR nodes and vars (+ single negations)"""
        if isinstance(term, CFVar):
            pat: Pattern = MetaVar(term.id)
            if term.negated:
                pat = neg(pat)
            phi_imp_phi = self.prop.imp_refl(pat)
            return term, phi_imp_phi, phi_imp_phi
        elif isinstance(term, CFOr):
            if term.negated:
                term.left.negated = not term.left.negated
                term.right.negated = not term.right.negated
                term_l, term_l_pf1, term_l_pf2 = self.propag_neg(term.left)
                term_r, term_r_pf1, term_r_pf2 = self.propag_neg(term.right)
                if not term.left.negated:
                    term_l_pf1 = self.prop.dni_l_i(term_l_pf1)
                    term_l_pf2 = self.prop.dni_r_i(term_l_pf2)
                ret_pf1 = self.prop.imim_and(term_l_pf1, term_r_pf1)
                ret_pf2 = self.prop.imim_and(term_l_pf2, term_r_pf2)
                if term.right.negated:
                    pf1_l, _ = Implies.extract(ret_pf1.conc)
                    a1, nb1 = And.extract(pf1_l)
                    b1 = Negation.extract(nb1)[0]
                    ret_pf1 = self.prop.imp_transitivity(self.prop.con3_i(self.prop.dne_r(a1, b1)), ret_pf1)
                    _, pf2_r = Implies.extract(ret_pf2.conc)
                    a2, nb2 = And.extract(pf2_r)
                    b2 = Negation.extract(nb2)[0]
                    ret_pf2 = self.prop.imp_transitivity(ret_pf2, self.prop.con3_i(self.prop.dni_r(a2, b2)))
                return CFAnd(term_l, term_r), ret_pf1, ret_pf2
            else:
                term_l, term_l_pf1, term_l_pf2 = self.propag_neg(term.left)
                term_r, term_r_pf1, term_r_pf2 = self.propag_neg(term.right)
                return (
                    CFOr(term_l, term_r),
                    self.prop.imim_or(term_l_pf1, term_r_pf1),
                    self.prop.imim_or(term_l_pf2, term_r_pf2),
                )
        else:
            raise AssertionError(
                f'Unexpected pattern! Expected a term with only Or, And and Not but got:\n{str(term)}\n'
            )

    def to_cnf(self, term: ConjForm) -> tuple[ConjForm, ProofThunk, ProofThunk]:
        """Assumes negation has been fully propagated through the term"""
        if isinstance(term, CFVar):
            pat: Pattern = MetaVar(term.id)
            if term.negated:
                pat = neg(pat)
            phi_imp_phi = self.prop.imp_refl(pat)
            return term, phi_imp_phi, phi_imp_phi
        elif isinstance(term, CFAnd):
            term_l, term_l_pf1, term_l_pf2 = self.to_cnf(term.left)
            term_r, term_r_pf1, term_r_pf2 = self.to_cnf(term.right)
            ret_pf1 = self.prop.imim_and(term_l_pf1, term_r_pf1)
            ret_pf2 = self.prop.imim_and(term_l_pf2, term_r_pf2)
            return CFAnd(term_l, term_r), ret_pf1, ret_pf2
        elif isinstance(term, CFOr):
            term_l, term_l_pf1, term_l_pf2 = self.to_cnf(term.left)
            term_r, term_r_pf1, term_r_pf2 = self.to_cnf(term.right)
            ret_pf1 = self.prop.imim_or(term_l_pf1, term_r_pf1)
            ret_pf2 = self.prop.imim_or(term_l_pf2, term_r_pf2)
            Implies.extract(ret_pf1.conc)
            if isinstance(term_l, CFAnd):
                ret_pf1 = self.imp_trans_match2(ret_pf1, self.or_distr_r())
                ret_pf2 = self.imp_trans_match1(self.or_distr_r_rev(), ret_pf2)
                new_term, pf1_, pf2_ = self.to_cnf(CFAnd(CFOr(term_l.left, term_r), CFOr(term_l.right, term_r)))
                ret_pf1 = self.prop.imp_transitivity(ret_pf1, pf1_)
                ret_pf2 = self.prop.imp_transitivity(pf2_, ret_pf2)
                return new_term, ret_pf1, ret_pf2
            elif isinstance(term_r, CFAnd):
                ret_pf1 = self.imp_trans_match2(ret_pf1, self.or_distr_l())
                ret_pf2 = self.imp_trans_match1(self.or_distr_l_rev(), ret_pf2)
                new_term, pf1_, pf2_ = self.to_cnf(CFAnd(CFOr(term_l, term_r.left), CFOr(term_l, term_r.right)))
                ret_pf1 = self.prop.imp_transitivity(ret_pf1, pf1_)
                ret_pf2 = self.prop.imp_transitivity(pf2_, ret_pf2)
                return new_term, ret_pf1, ret_pf2
            else:
                return CFOr(term_l, term_r), ret_pf1, ret_pf2
        else:
            raise AssertionError(f'Unexpected pattern! Expected a term with only Or and And but got:\n{str(term)}\n')

    def to_clauses(self, term: ConjForm) -> tuple[ClauseConjunction, ProofThunk, ProofThunk]:
        """Assumes term is in CNF form"""
        if isinstance(term, CFVar):
            if term.negated:
                id = -(term.id + 1)
            else:
                id = term.id + 1
            pat: Pattern = MetaVar(term.id)
            if term.negated:
                pat = neg(pat)
            phi_imp_phi = self.prop.imp_refl(pat)
            return [[id]], phi_imp_phi, phi_imp_phi
        elif isinstance(term, CFAnd):
            term_l, term_l_pf1, term_l_pf2 = self.to_clauses(term.left)
            term_r, term_r_pf1, term_r_pf2 = self.to_clauses(term.right)
            ret_pf1 = self.prop.imim_and(term_l_pf1, term_r_pf1)
            ret_pf2 = self.prop.imim_and(term_l_pf2, term_r_pf2)
            l = len(term_l)
            assert l > 0
            if l > 1:
                shift_right: ProofThunk = self.and_assoc_r()
                shift_left: ProofThunk = self.and_assoc_l()
                for i in range(0, l - 2):
                    shift_right = self.imp_trans_match1(
                        self.and_assoc_r(), self.prop.imim_and_r(MetaVar(i + 3), shift_right)
                    )
                    shift_left = self.imp_trans_match2(
                        self.prop.imim_and_r(MetaVar(i + 3), shift_left), self.and_assoc_l()
                    )
                ret_pf1 = self.imp_trans_match2(ret_pf1, shift_right)
                ret_pf2 = self.imp_trans_match1(shift_left, ret_pf2)
            return term_l + term_r, ret_pf1, ret_pf2
        elif isinstance(term, CFOr):
            term_l, term_l_pf1, term_l_pf2 = self.to_clauses(term.left)
            term_r, term_r_pf1, term_r_pf2 = self.to_clauses(term.right)
            ret_pf1 = self.prop.imim_or(term_l_pf1, term_r_pf1)
            ret_pf2 = self.prop.imim_or(term_l_pf2, term_r_pf2)
            assert len(term_l) == 1
            assert len(term_r) == 1
            l = len(term_l[0])
            assert l > 0
            if l > 1:
                shift_right = self.or_assoc_r()
                shift_left = self.or_assoc_l()
                for i in range(0, l - 2):
                    shift_right = self.imp_trans_match1(
                        self.or_assoc_r(), self.prop.imim_or_r(MetaVar(i + 3), shift_right)
                    )
                    shift_left = self.imp_trans_match2(
                        self.prop.imim_or_r(MetaVar(i + 3), shift_left), self.or_assoc_l()
                    )
                ret_pf1 = self.imp_trans_match2(ret_pf1, shift_right)
                ret_pf2 = self.imp_trans_match1(shift_left, ret_pf2)
            return [term_l[0] + term_r[0]], ret_pf1, ret_pf2
        else:
            raise AssertionError(
                f'Unexpected pattern! Expected a term with only Or, And and Negations but got:\n{str(term)}\n'
            )

    def conjunction_implies_nth(self, term: Pattern, n: int, l: int) -> ProofThunk:
        """p0 /\\ (p1 /\\ (... /\\ pl)) -> pn"""
        assert 0 <= n < l
        if l == 1:
            return self.imp_refl(term)
        head, term = And.extract(term)
        if n == 0:
            return self.and_l_imp(head, term)
        return self.imp_transitivity(self.and_r_imp(head, term), self.conjunction_implies_nth(term, n - 1, l - 1))

    def ac_move_to_front(  # noqa: N802
        self,
        positions: Clause,  # Sorted list of unique indices in the range [0, len(terms))
        terms: list[Pattern],
        assoc: Callable[[Pattern, Pattern, Pattern], ProofThunk],
        comm: Callable[[Pattern, Pattern], ProofThunk],
        cong: Callable[[ProofThunk, ProofThunk], ProofThunk],
        op: Callable[[Pattern, Pattern], Pattern],
        extract_op: Callable[[Pattern], tuple[Pattern, ...]],
    ) -> ProofThunk:
        """
        Produces a proof of
        p0 . (p1 . (p2 . (... px1 .  (... pxn . (... . pn)))) <->
        px1 . (px2 . (... . (pxn . (p0 . (p1 . (... px-1 . (px+1 . (... . pn)))))))
        where . represents the binary operation op
        positions is a list of unique indices in the range(len(terms)) that should be swapped to the front
        assoc is of the form: p . (q . r) <-> (p . q) . r
        comm is of the form: p . q <-> q . p
        cong is of the form:
            p <-> q   r <-> s
          ---------------------
            p . r <-> q . s
        extract_op breaks an op application into its two children
        """
        assoc_rev = lambda a, b, c: self.equiv_sym(assoc(a, b, c))

        def unroll(term_l: Pattern, term_r: Pattern, positions: Clause, l: int, unrolling: int = 0) -> ProofThunk:
            if not positions:
                return self.equiv_refl(op(term_l, term_r))
            pos = positions[0]
            assert unrolling + 1 < l
            assert pos < l
            if pos <= unrolling:
                if unrolling == 0:
                    if l == 2:
                        return self.equiv_refl(op(term_l, term_r))
                    mid, term_r = extract_op(term_r)
                    rec_pf = unroll(mid, term_r, positions[1:], l - 1)
                    return cong(self.equiv_refl(term_l), rec_pf)
                term_l, mid = extract_op(term_l)
                if pos == unrolling:
                    pf = cong(comm(term_l, mid), self.equiv_refl(term_r))
                    pf = self.equiv_transitivity(pf, assoc_rev(mid, term_l, term_r))
                    rec_pf = unroll(term_l, term_r, positions[1:], l - 1, unrolling - 1)
                    return self.equiv_transitivity(pf, cong(self.equiv_refl(mid), rec_pf))
                rec_pf = unroll(term_l, op(mid, term_r), positions, l, unrolling - 1)
                return self.equiv_transitivity(assoc_rev(term_l, mid, term_r), rec_pf)
            if l == 2:
                return comm(term_l, term_r)
            if unrolling == l - 2:
                pf = comm(term_l, term_r)
                term_l, mid = extract_op(term_l)
                rec_pf = unroll(term_l, mid, positions[1:], l - 1, l - 3)
                return self.equiv_transitivity(pf, cong(self.equiv_refl(term_r), rec_pf))
            mid, term_r = extract_op(term_r)
            pf = assoc(term_l, mid, term_r)
            rec_pf = unroll(op(term_l, mid), term_r, positions, l, unrolling + 1)
            return self.equiv_transitivity(pf, rec_pf)

        if len(terms) == 1:
            return self.equiv_refl(terms[0])
        sorted_pos = sorted(positions)
        for i in range(len(positions)):
            sorted_pos[i] = sorted_pos[i] - i
        sorted_pos.append(0)
        return unroll(terms[0], foldr_op(op, terms, 1), sorted_pos, len(terms))

    def or_move_to_front(self, pos: Clause, terms: list[Pattern]) -> ProofThunk:
        return self.ac_move_to_front(pos, terms, self.or_assoc, self.or_comm, self.or_cong, Or, Or.extract)

    def and_move_to_front(self, pos: Clause, terms: list[Pattern]) -> ProofThunk:
        return self.ac_move_to_front(pos, terms, self.and_assoc, self.and_comm, self.and_cong, And, And.extract)

    def or_idem(self, p: Pattern = phi0) -> ProofThunk:
        """p \\/ p <-> p"""
        return self.prop.and_intro(self.prop.peirce_bot(p), self.prop.prop1_inst(p, neg(p)))

    def reduce_or_duplicates_at_front(self, p: Pattern = phi0, q: Pattern = phi1) -> ProofThunk:
        """p \\/ (p \\/ q) <-> p \\/ q"""
        return self.equiv_transitivity(
            self.or_assoc(p, p, q),
            self.prop.and_intro(
                self.prop.imim_or_l(q, self.prop.peirce_bot(p)), self.prop.imim_or_l(q, self.prop.prop1_inst(p, neg(p)))
            ),
        )

    def reduce_n_or_duplicates_at_front(self, n: int, terms: list[Pattern]) -> ProofThunk:
        """p \\/ (p  ... (p \\/ q)) <-> p \\/ q"""
        assert 0 <= n < len(terms)
        if n == 0:
            return self.equiv_refl(foldr_op(Or, terms))
        p = terms[0]
        if len(terms) == n + 1:
            q = p
            pf = self.or_idem(p)
        else:
            q = foldr_op(Or, terms, n + 1)
            pf = self.reduce_or_duplicates_at_front(p, q)
            q = Or(p, q)
        for _ in range(n - 1):
            pf = self.equiv_transitivity(self.reduce_or_duplicates_at_front(p, q), pf)
            q = Or(p, q)
        return pf

    def simplify_clause(self, cl: Clause, resolvent: int) -> tuple[Clause, ProofThunk]:
        positions = []
        stripped_cl = []
        for i in range(len(cl)):
            if cl[i] == resolvent:
                positions.append(i)
            else:
                stripped_cl.append(cl[i])
        if not positions:
            return cl, self.equiv_refl(clause_to_pattern(cl))
        n_pos = len(positions)
        pf = self.or_move_to_front(positions, [id_to_metavar(id) for id in cl])
        intermed_cl = ([resolvent] * n_pos) + stripped_cl
        pf = self.equiv_transitivity(
            pf, self.reduce_n_or_duplicates_at_front(n_pos - 1, [id_to_metavar(id) for id in intermed_cl])
        )
        return ([resolvent] + stripped_cl), pf

    # Returns None if the sets cannot be resolved.
    # Otherwise it returns the resolvent of the two sets
    # which may be negative if the order of the sets needs to be swapped
    # as well as the resulting clause
    def resolvable(self, c1: frozenset[int], c2: frozenset[int]) -> tuple[int, frozenset[int]] | None:
        common = {-x for x in c1}.intersection(c2)
        if len(common) != 1:
            return None
        [resolvent] = common
        c1 = c1.difference({-resolvent})
        c2 = c2.difference({resolvent})
        return resolvent, c1.union(c2)

    def merge_clauses(self, term_l: Pattern, len_l: int, term_r: Pattern) -> ProofThunk:
        if len_l == 1:
            return self.equiv_refl(Or(term_l, term_r))
        l1, l2 = Or.extract(term_l)
        if len_l == 2:
            return self.equiv_sym(self.or_assoc(l1, l2, term_r))
        return self.equiv_transitivity(
            self.equiv_sym(self.or_assoc(l1, l2, term_r)),
            self.or_cong(self.equiv_refl(l1), self.merge_clauses(l2, len_l - 1, term_r)),
        )

    def resolution_algorithm(self, hint: ResolutionHint, l: list[frozenset[int]]) -> bool:
        for cl1 in l:
            for cl2 in l:
                if cl2 == cl1:
                    break
                res = self.resolvable(cl1, cl2)
                if res is None:
                    continue
                resolvant, res_set = res
                if not res_set in hint:
                    if resolvant < 0:
                        cl1, cl2 = cl2, cl1
                        resolvant = -resolvant
                    hint[res_set] = ResolutionHintSource(cl1, cl2, resolvant)
                    if not res_set:
                        return True
                    l.append(res_set)
        return False

    def is_trivial_clause(self, cl: frozenset[int]) -> bool:
        l = list(cl)
        for x1, x2 in combinations(l, 2):
            if x1 + x2 == 0:
                return True
        return False

    def prove_trivial_clause(self, cl: list[int]) -> ProofThunk:
        for (i1, x1), (i2, x2) in combinations(enumerate(cl), 2):
            if x1 + x2 == 0:
                neg_first = (x1 < x2) == (i1 < i2)
                id = abs(x1)
                pos = [i1, i2]
                break
        id_term = id_to_metavar(id)
        if len(cl) == 2:
            if neg_first:
                return self.dneg_elim(id_term)
            return self.imp_refl(neg(id_term))
        pf = self.and_r(self.or_move_to_front(pos, [id_to_metavar(x) for x in cl]))
        rest_cl = [x for (i, x) in enumerate(cl) if i not in pos]
        rest = clause_to_pattern(rest_cl)
        if neg_first:
            pf = self.imp_transitivity(self.or_assoc_r(neg(id_term), id_term, rest), pf)
            pf2 = self.or_l(self.dneg_elim(id_term), rest)
        else:
            pf = self.imp_transitivity(self.or_assoc_r(id_term, neg(id_term), rest), pf)
            pf2 = self.or_l(self.imp_refl(neg(id_term)), rest)
        return self.mp(pf, pf2)

    def build_proof_from_hint(
        self, hint: ResolutionHint, cl: frozenset[int], terms: list[list[int]]
    ) -> tuple[list[int], ProofThunk]:
        res = hint[cl]
        if isinstance(res, ResolutionHintSource):
            resolvant = res.resolvant
            resolvant_term = id_to_metavar(resolvant)
            term_l, pf_l = self.build_proof_from_hint(hint, res.left_set, terms)
            term_r, pf_r = self.build_proof_from_hint(hint, res.right_set, terms)
            term_l, simplify_l = self.simplify_clause(term_l, -resolvant)
            term_r, simplify_r = self.simplify_clause(term_r, resolvant)
            assert term_l[0] == -resolvant
            assert term_r[0] == resolvant
            term_l_rest = term_l[1:]
            term_r_rest = term_r[1:]
            final_term = term_l_rest + term_r_rest
            assert frozenset(final_term) == cl
            pf_l = self.imp_transitivity(pf_l, self.and_l(simplify_l))
            pf_r = self.imp_transitivity(pf_r, self.and_l(simplify_r))
            match (len(term_l_rest) == 0), (len(term_r_rest) == 0):
                case False, False:
                    term_l_pat = clause_to_pattern(term_l_rest)
                    term_r_pat = clause_to_pattern(term_r_rest)
                    pf = self.resolution(resolvant_term, term_l_pat, term_r_pat)
                    pf = self.imp_transitivity(
                        pf,
                        self.and_l(self.merge_clauses(term_l_pat, len(term_l_rest), term_r_pat)),
                    )
                case False, True:
                    pf = self.resolution_l(resolvant_term, clause_to_pattern(term_l_rest))
                case True, False:
                    pf = self.resolution_r(resolvant_term, clause_to_pattern(term_r_rest))
                case True, True:
                    pf = self.resolution_base(resolvant_term)
            pf = self.resolution_step(pf_l, pf_r, pf)
            return final_term, pf
        term = clause_list_to_pattern(terms)
        return terms[res], self.conjunction_implies_nth(term, res, len(terms))

    # The returned boolean represents whether the proof is a proof of the original formula (True) or its negation (False)
    def start_resolution_algorithm(self, clauses: list[list[int]]) -> tuple[bool, ProofThunk] | None:
        if not clauses:
            return True, self.top_intro()
        resolution_list = [frozenset(cl) for cl in clauses]
        hint: ResolutionHint = {}
        for index, cl_set in enumerate(resolution_list):
            if not self.is_trivial_clause(cl_set):
                hint[cl_set] = index
        if not hint:
            if len(clauses) == 1:
                return True, self.prove_trivial_clause(clauses[0])
            pfs = [self.prove_trivial_clause(cl) for cl in clauses]
            prf = self.and_intro(pfs[-2], pfs[-1])
            for pf in reversed(pfs[:-2]):
                prf = self.and_intro(pf, prf)
            return True, prf
        if not self.resolution_algorithm(hint, list(hint.keys())):
            # Inconclusive result, the original pattern is most likely not
            # a tautology and nor is its negation
            return None
        ret_bool = False
        ret_list, pf = self.build_proof_from_hint(hint, frozenset([]), clauses)
        assert not ret_list
        return ret_bool, pf
