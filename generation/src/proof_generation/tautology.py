from __future__ import annotations

from functools import partial
from typing import TYPE_CHECKING

from proof_generation.pattern import Implies, MetaVar, Notation, match_single
from proof_generation.proof import ProofThunk
from proof_generation.proofs.propositional import (
    And,
    Equiv,
    Negation,
    Or,
    Propositional,
    bot,
    neg,
    phi0,
    phi1,
    phi2,
    top,
)

if TYPE_CHECKING:
    from proof_generation.pattern import Pattern


# Structure of Conjunctive Form Tree
class ConjTerm:
    negated: bool

    def __init__(self, negated: bool):
        self.negated = negated

    def __str__(self) -> str:
        return str(conj_to_pattern(self))


class ConjAnd(ConjTerm):
    left: ConjTerm
    right: ConjTerm

    def __init__(self, left: ConjTerm, right: ConjTerm):
        super().__init__(False)
        self.left = left
        self.right = right


class ConjOr(ConjTerm):
    left: ConjTerm
    right: ConjTerm

    def __init__(self, left: ConjTerm, right: ConjTerm):
        super().__init__(False)
        self.left = left
        self.right = right


class ConjBool(ConjTerm):
    pass


class ConjVar(ConjTerm):
    id: int

    def __init__(self, id: int):
        super().__init__(False)
        self.id = id


def conj_to_pattern(term: ConjTerm) -> Pattern:
    pat: Pattern
    if isinstance(term, ConjBool):
        pat = bot
    elif isinstance(term, ConjVar):
        pat = MetaVar(term.id)
    elif isinstance(term, ConjOr):
        pat = Or(conj_to_pattern(term.left), conj_to_pattern(term.right))
    elif isinstance(term, ConjAnd):
        pat = And(conj_to_pattern(term.left), conj_to_pattern(term.right))
    if term.negated:
        pat = neg(pat)
    return pat


def id_to_metavar(id: int) -> Pattern:
    assert id != 0
    if id < 0:
        return neg(MetaVar(-(id + 1)))
    return MetaVar(id - 1)


def clause_to_pattern(l: list[int]) -> Pattern:
    assert len(l) > 0
    pat = id_to_metavar(l[0])
    if len(l) > 1:
        pat = Or(pat, clause_to_pattern(l[1:]))
    return pat


def clause_list_to_pattern(l: list[list[int]]) -> Pattern:
    assert len(l) > 0
    pat = clause_to_pattern(l[0])
    if len(l) > 1:
        pat = And(pat, clause_list_to_pattern(l[1:]))
    return pat


class Tautology(Propositional):
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
            Equiv(And(phi0, phi1), And(phi1, phi0)),
        ]

    def imp_trans_match1(self, h1: ProofThunk, h2: ProofThunk) -> ProofThunk:
        """Same as imp_transitivity but h1 is instantiated to match h2"""
        _, b = Implies.extract(h1.conc)
        c, _ = Implies.extract(h2.conc)
        subst = match_single(b, c, {})
        assert subst is not None
        actual_subst: dict[int, Pattern] = subst
        return self.imp_transitivity(
            ProofThunk(partial(self.dynamic_inst, h1, actual_subst), h1.conc.instantiate(actual_subst)), h2
        )

    def imp_trans_match2(self, h1: ProofThunk, h2: ProofThunk) -> ProofThunk:
        """Same as imp_transitivity but h2 is instantiated to match h1"""
        _, b = Implies.extract(h1.conc)
        c, _ = Implies.extract(h2.conc)
        subst = match_single(c, b, {})
        assert subst is not None
        actual_subst: dict[int, Pattern] = subst
        return self.imp_transitivity(
            h1, ProofThunk(partial(self.dynamic_inst, h2, actual_subst), h2.conc.instantiate(actual_subst))
        )

    def mpcom(self, p_pf: ProofThunk, q: Pattern) -> ProofThunk:
        """
               p
        -----------------
          (p -> q) -> q
        """
        p = p_pf.conc
        pq = Implies(p, q)
        return self.mp(self.mp(self.p2(pq, p, q), self.imp_refl(pq)), self.imp_provable(pq, p_pf))

    def dni_l(self, p: Pattern, q: Pattern) -> ProofThunk:
        """(p -> q) -> (~~p -> q)"""
        return self.mp(self.imp_trans(neg(neg(p)), p, q), self.dneg_elim(p))

    def dni_l_i(self, pq_pf: ProofThunk) -> ProofThunk:
        """
            p -> q
        --------------
          ~~p -> q
        """
        p, q = Implies.extract(pq_pf.conc)
        return self.mp(self.dni_l(p, q), pq_pf)

    def dni_r(self, p: Pattern, q: Pattern) -> ProofThunk:
        """(p -> q) -> (p -> ~~q)"""
        return self.mp(self.p2(p, q, neg(neg(q))), self.imp_provable(p, self.dneg_intro(q)))

    def dni_r_i(self, pq_pf: ProofThunk) -> ProofThunk:
        """
           p -> q
        --------------
          p -> ~~q
        """
        p, q = Implies.extract(pq_pf.conc)
        return self.mp(self.dni_r(p, q), pq_pf)

    def dne_l(self, p: Pattern, q: Pattern) -> ProofThunk:
        """(~~p -> q) -> (p -> q)"""
        return self.mp(self.imp_trans(p, neg(neg(p)), q), self.dneg_intro(p))

    def dne_l_i(self, pq_pf: ProofThunk) -> ProofThunk:
        """
          ~~p -> q
        --------------
            p -> q
        """
        p, q = Implies.extract(pq_pf.conc)
        return self.mp(self.dne_l(p, q), pq_pf)

    def dne_r(self, p: Pattern, q: Pattern) -> ProofThunk:
        """(p -> ~~q) -> (p -> q)"""
        return self.mp(self.p2(p, neg(neg(q)), q), self.imp_provable(p, self.dneg_elim(q)))

    def dne_r_i(self, pq_pf: ProofThunk) -> ProofThunk:
        """
          p -> ~~q
        --------------
           p -> q
        """
        p, q = Implies.extract(pq_pf.conc)
        return self.mp(self.dne_r(p, q), pq_pf)

    def helper1(self, p_pf: ProofThunk, qr_pf: ProofThunk) -> ProofThunk:
        """
           p    q -> r
        -----------------
          (p -> q) -> r
        """
        q, _ = Implies.extract(qr_pf.conc)
        return self.imp_transitivity(self.mpcom(p_pf, q), qr_pf)

    def a1d(self, pq_pf: ProofThunk, r: Pattern) -> ProofThunk:
        """
             p -> q
        ---------------
          p -> r -> q
        """
        _, q = Implies.extract(pq_pf.conc)
        return self.imp_transitivity(pq_pf, self.p1(q, r))

    def con3(self, p: Pattern, q: Pattern) -> ProofThunk:
        """(p -> q) -> (~q -> ~p)"""
        return self.imp_trans(p, q, bot)

    def con3_i(self, pq_pf: ProofThunk) -> ProofThunk:
        """
          p -> q
        ------------
          ~q -> ~p
        """
        p, q = Implies.extract(pq_pf.conc)
        return self.mp(self.con3(p, q), pq_pf)

    def absurd2(self, pq_pf: ProofThunk, r: Pattern) -> ProofThunk:
        """
             p -> q
        -----------------
           ~q -> p -> r
        """
        p, q = Implies.extract(pq_pf.conc)
        return self.imp_transitivity(self.absurd(q, r), self.mp(self.imp_trans(p, q, r), pq_pf))

    def lemma1(self, q: Pattern, pf: ProofThunk) -> ProofThunk:
        """
                ~p
        ------------------
          (q -> p) -> ~q
        """
        p = Negation.extract(pf.conc)[0]
        return self.mp(self.p2(q, p, bot), self.imp_provable(q, pf))

    def con1(self, pf: ProofThunk) -> ProofThunk:
        """
          ~p -> q
        -----------
          ~q -> p
        """
        np, q = Implies.extract(pf.conc)
        p = Negation.extract(np)[0]
        return self.imp_transitivity(
            self.mp(self.ant_commutativity(self.imp_transitivity(self.p1(neg(q), np), self.p2(np, q, bot))), pf),
            self.dneg_elim(p),
        )

    def absurd3(self, npq_pf: ProofThunk, nr_pf: ProofThunk) -> ProofThunk:
        """
           ~p -> q     ~r
        -------------------
           (q -> r) -> p
        """
        _, q = Implies.extract(npq_pf.conc)
        return self.imp_transitivity(self.lemma1(q, nr_pf), self.con1(npq_pf))

    def absurd4(self, pnq_pf: ProofThunk, r: Pattern) -> ProofThunk:
        """
           p -> ~q
        ------------------
           q -> p -> r
        """
        _, nq = Implies.extract(pnq_pf.conc)
        q = Negation.extract(nq)[0]
        return self.imp_transitivity(self.dneg_intro(q), self.absurd2(pnq_pf, r))

    def absurd_i(self, np_pf: ProofThunk, q: Pattern) -> ProofThunk:
        """
           ~p
        -----------
          p -> q
        """
        p = Negation.extract(np_pf.conc)[0]
        return self.mp(self.absurd(p, q), np_pf)

    def and_not_r_intro(self, p_pf: ProofThunk, nq_pf: ProofThunk) -> ProofThunk:
        """
           p   ~q
        -------------
          ~(p -> q)
        """
        p_pf.conc
        q = Negation.extract(nq_pf.conc)[0]
        return self.imp_transitivity(self.mpcom(p_pf, q), nq_pf)

    def imim_l(self, pat: Pattern, h: ProofThunk) -> ProofThunk:
        """
              a -> b
        ---------------------
        (b -> c) -> (a -> c)
        """
        a, b = Implies.extract(h.conc)
        return self.mp(self.imp_trans(a, b, pat), h)

    def imim(self, h1: ProofThunk, h2: ProofThunk) -> ProofThunk:
        """
        (a -> b)    (c -> d)
        ---------------------
        (b -> c) -> (a -> d)
        """
        a, b = Implies.extract(h1.conc)
        c, d = Implies.extract(h2.conc)
        return self.imp_transitivity(self.imim_l(c, h1), self.mp(self.p2(a, c, d), self.imp_provable(a, h2)))

    def imim_r(self, pat: Pattern, h: ProofThunk) -> ProofThunk:
        """
              a -> b
        ---------------------
        (c -> a) -> (c -> b)
        """
        return self.imim(self.imp_refl(pat), h)

    def imim_nnr(self, h1: ProofThunk, h2: ProofThunk) -> ProofThunk:
        """
        (a -> b)    (c -> d)
        ---------------------
        (b -> c) -> (~~a -> d)
        """
        a, b = Implies.extract(h1.conc)
        c, d = Implies.extract(h2.conc)
        return self.imp_transitivity(self.imim(h1, h2), self.mp(self.imp_trans(neg(neg(a)), a, d), self.dneg_elim(a)))

    def imim_nnl(self, h1: ProofThunk, h2: ProofThunk) -> ProofThunk:
        """
        (a -> b)    (c -> d)
        ---------------------
        (~~b -> c) -> (a -> d)
        """
        a, b = Implies.extract(h1.conc)
        c, d = Implies.extract(h2.conc)
        return self.imp_transitivity(self.mp(self.imp_trans(b, neg(neg(b)), c), self.dneg_intro(b)), self.imim(h1, h2))

    def imim_or(self, h1: ProofThunk, h2: ProofThunk) -> ProofThunk:
        """
        (a -> b)   (c -> d)
        ---------------------
        a \\/ c -> b \\/ d
        """
        return self.imim(self.con3_i(h1), h2)

    def imim_and(self, h1: ProofThunk, h2: ProofThunk) -> ProofThunk:
        """
        (a -> b)   (c -> d)
        ---------------------
        a /\\ c -> b /\\ d
        """
        return self.con3_i(self.imim(h1, self.con3_i(h2)))

    def imim_and_r(self, pat: Pattern, h: ProofThunk) -> ProofThunk:
        """
           (b -> c)
        ---------------------
           a /\\ b -> a /\\ c
        """
        return self.imim_and(self.imp_refl(pat), h)

    def imim_and_l(self, pat: Pattern, h: ProofThunk) -> ProofThunk:
        """
            (a -> b)
        ---------------------
           a /\\ c -> b /\\ c
        """
        return self.imim_and(h, self.imp_refl(pat))

    def imim_or_r(self, pat: Pattern, h: ProofThunk) -> ProofThunk:
        """
             (b -> c)
        ---------------------
            a \\/ b -> a \\/ c
        """
        return self.imim(self.imp_refl(neg(pat)), h)

    def imim_or_l(self, pat: Pattern, h: ProofThunk) -> ProofThunk:
        """
              (a -> b)
        ---------------------
           a \\/ c -> b \\/ c
        """
        return self.imim(self.con3_i(h), self.imp_refl(pat))

    def and_intro(self, p_pf: ProofThunk, q_pf: ProofThunk) -> ProofThunk:
        """
            p   q
        ------------
           p /\\ q
        """
        q = q_pf.conc
        return self.imp_transitivity(self.mpcom(p_pf, neg(q)), self.mp(self.dneg_intro(q), q_pf))

    def and_assoc_r(self, pat1: Pattern = phi0, pat2: Pattern = phi1, pat3: Pattern = phi2) -> ProofThunk:
        """(a /\\ b) /\\ c -> a /\\ (b /\\ c)"""
        return self.load_ax(0, pat1, pat2, pat3)

    def and_assoc_l(self, pat1: Pattern = phi0, pat2: Pattern = phi1, pat3: Pattern = phi2) -> ProofThunk:
        """a /\\ (b /\\ c) -> (a /\\ b) /\\ c"""
        return self.load_ax(1, pat1, pat2, pat3)

    def or_assoc_r(self, pat1: Pattern = phi0, pat2: Pattern = phi1, pat3: Pattern = phi2) -> ProofThunk:
        """(a \\/ b) \\/ c -> a \\/ (b \\/ c)"""
        return self.load_ax(2, pat1, pat2, pat3)

    def or_assoc_l(self, pat1: Pattern = phi0, pat2: Pattern = phi1, pat3: Pattern = phi2) -> ProofThunk:
        """a \\/ (b \\/ c) -> (a \\/ b) \\/ c"""
        return self.load_ax(3, pat1, pat2, pat3)

    def or_distr_r(self, pat1: Pattern = phi0, pat2: Pattern = phi1, pat3: Pattern = phi2) -> ProofThunk:
        """(a /\\ b) \\/ c -> (a \\/ c) /\\ (b \\/ c)"""
        return self.load_ax(4, pat1, pat2, pat3)

    def or_distr_r_rev(self, pat1: Pattern = phi0, pat2: Pattern = phi1, pat3: Pattern = phi2) -> ProofThunk:
        """(a \\/ c) /\\ (b \\/ c) -> (a /\\ b) \\/ c"""
        return self.load_ax(5, pat1, pat2, pat3)

    def or_distr_l(self, pat1: Pattern = phi0, pat2: Pattern = phi1, pat3: Pattern = phi2) -> ProofThunk:
        """a \\/ (b /\\ c) -> (a \\/ b) /\\ (a \\/ c)"""
        return self.load_ax(6, pat1, pat2, pat3)

    def or_distr_l_rev(self, pat1: Pattern = phi0, pat2: Pattern = phi1, pat3: Pattern = phi2) -> ProofThunk:
        """(a \\/ b) /\\ (a \\/ c) -> a \\/ (b /\\ c)"""
        return self.load_ax(7, pat1, pat2, pat3)

    def and_assoc(self, pat1: Pattern = phi0, pat2: Pattern = phi1, pat3: Pattern = phi2) -> ProofThunk:
        """a /\\ (b /\\ c) <-> (a /\\ b) /\\ c"""
        return self.and_intro(self.and_assoc_l(pat1, pat2, pat3), self.and_assoc_r(pat1, pat2, pat3))

    def or_assoc(self, pat1: Pattern = phi0, pat2: Pattern = phi1, pat3: Pattern = phi2) -> ProofThunk:
        """a \\/ (b \\/ c) <-> (a \\/ b) \\/ c"""
        return self.and_intro(self.or_assoc_l(pat1, pat2, pat3), self.or_assoc_r(pat1, pat2, pat3))

    def and_comm(self, p: Pattern = phi0, q: Pattern = phi1) -> ProofThunk:
        """p /\\ q <-> q /\\ p"""
        return self.load_ax(8, p, q)

    def or_comm_imp(self, p: Pattern = phi0, q: Pattern = phi1) -> ProofThunk:
        """p \\/ q -> q \\/ p"""
        return self.imp_transitivity(self.imp_trans(neg(p), q, bot), self.dne_r(neg(q), p))

    def or_comm(self, p: Pattern = phi0, q: Pattern = phi1) -> ProofThunk:
        """p \\/ q <-> q \\/ p"""
        return self.and_intro(self.or_comm_imp(p, q), self.or_comm_imp(q, p))

    def and_l_imp(self, p: Pattern = phi0, q: Pattern = phi1) -> ProofThunk:
        """p /\\ q -> p"""
        return self.con1(self.absurd(p, neg(q)))

    def and_l(self, pq_pf: ProofThunk) -> ProofThunk:
        """
           p /\\ q
        ------------
              p
        """
        p, q = And.extract(pq_pf.conc)
        return self.mp(self.and_l_imp(p, q), pq_pf)

    def and_r_imp(self, p: Pattern = phi0, q: Pattern = phi1) -> ProofThunk:
        """p /\\ q -> q"""
        return self.con1(self.p1(neg(q), p))

    def and_r(self, pq_pf: ProofThunk) -> ProofThunk:
        """
           p /\\ q
        ------------
              q
        """
        p, q = And.extract(pq_pf.conc)
        return self.mp(self.and_r_imp(p, q), pq_pf)

    def equiv_refl(self, p: Pattern = phi0) -> ProofThunk:
        """p <-> p"""
        pf = self.imp_refl(p)
        return self.and_intro(pf, pf)

    def equiv_sym(self, pf: ProofThunk) -> ProofThunk:
        """
          p <-> q
        -----------
          q <-> p
        """
        return self.and_intro(self.and_r(pf), self.and_l(pf))

    def equiv_transitivity(self, pq_pf: ProofThunk, qr_pf: ProofThunk) -> ProofThunk:
        """
           p <-> q    q <-> r
        ----------------------
                p <-> r
        """
        return self.and_intro(
            self.imp_transitivity(self.and_l(pq_pf), self.and_l(qr_pf)),
            self.imp_transitivity(self.and_r(qr_pf), self.and_r(pq_pf)),
        )

    def equiv_trans_match1(self, h1: ProofThunk, h2: ProofThunk) -> ProofThunk:
        """Same as equiv_transitivity but h1 is instantiated to match h2"""
        _, b = Equiv.extract(h1.conc)
        c, _ = Equiv.extract(h2.conc)
        subst = match_single(b, c, {})
        assert subst is not None
        actual_subst: dict[int, Pattern] = subst
        return self.equiv_transitivity(
            ProofThunk(partial(self.dynamic_inst, h1, actual_subst), h1.conc.instantiate(actual_subst)), h2
        )

    def equiv_trans_match2(self, h1: ProofThunk, h2: ProofThunk) -> ProofThunk:
        """Same as equiv_transitivity but h2 is instantiated to match h1"""
        _, b = Equiv.extract(h1.conc)
        c, _ = Equiv.extract(h2.conc)
        subst = match_single(c, b, {})
        assert subst is not None
        actual_subst: dict[int, Pattern] = subst
        return self.equiv_transitivity(
            h1, ProofThunk(partial(self.dynamic_inst, h2, actual_subst), h2.conc.instantiate(actual_subst))
        )

    def and_cong(self, pf1: ProofThunk, pf2: ProofThunk) -> ProofThunk:
        return self.and_intro(
            self.imim_and(self.and_l(pf1), self.and_l(pf2)),
            self.imim_and(self.and_r(pf1), self.and_r(pf2)),
        )

    def or_cong(self, pf1: ProofThunk, pf2: ProofThunk) -> ProofThunk:
        return self.and_intro(
            self.imim_or(self.and_l(pf1), self.and_l(pf2)),
            self.imim_or(self.and_r(pf1), self.and_r(pf2)),
        )

    def resolution(self, p: Pattern = phi0, a: Pattern = phi1, b: Pattern = phi2) -> ProofThunk:
        """~p \\/ a -> p \\/ b -> a \\/ b"""
        return self.imp_transitivity(self.or_comm_imp(neg(p), a), self.imp_trans(neg(a), neg(p), b))

    def resolution_r(self, p: Pattern = phi0, b: Pattern = phi1) -> ProofThunk:
        """~p -> p \\/ b -> b"""
        return self.ant_commutativity(self.imp_refl(Or(p, b)))

    def resolution_l(self, p: Pattern = phi0, a: Pattern = phi1) -> ProofThunk:
        """~p \\/ a -> p -> a"""
        return self.imim_l(a, self.dneg_intro(p))

    def resolution_base(self, p: Pattern = phi0) -> ProofThunk:
        """~p -> p -> bot"""
        return self.imp_refl(neg(p))

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
        return self.mp(self.mp(self.p2(a, c, d), self.imp_transitivity(ab_pf, bcd_pf)), ac_pf)

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
    def to_conj(self, pat: Pattern) -> tuple[ConjTerm, ProofThunk, ProofThunk | None]:
        """
        Assumes the input is a propositional formula and transforms it to one
        made up of only ORs, negations and variables
        Output is:
          the representation of the new term
          proof that old term -> new term
          proof that new term -> old term
        NOTE! When the new term is Top or Bottom, we only populate the
        first proof; this proof will be a proof of `old term` or `neg(old term)`
        respectively (as opposed to, say, `old term -> Top``)
        """
        if pat == bot:
            return ConjBool(False), self.top_intro(), None
        if pat == top:
            return ConjBool(True), self.top_intro(), None
        if isinstance(pat, MetaVar):
            phi_imp_phi = self.imp_refl(pat)
            return ConjVar(pat.name), phi_imp_phi, phi_imp_phi
        elif pat_imp := Implies.extract(pat):
            pat0 = pat_imp[0]
            pat1 = pat_imp[1]
            pat1_conj, pat1_l, pat1_r = self.to_conj(pat1)

            if isinstance(pat1_conj, ConjBool):
                if pat1_conj.negated:
                    pf = self.imp_provable(pat0, pat1_l)
                    return ConjBool(True), pf, None
                else:
                    pat0_conj, pat0_l, pat0_r = self.to_conj(pat0)
                    if isinstance(pat0_conj, ConjBool):
                        if pat0_conj.negated:
                            pf = self.and_not_r_intro(pat0_l, pat1_l)
                            return ConjBool(False), pf, None
                        else:
                            pf = self.absurd_i(pat0_l, pat1)
                            return ConjBool(True), pf, None
                    if pat0_conj.negated:
                        pat0_conj.negated = False
                        assert pat0_r is not None
                        actual_pat0_r: ProofThunk = pat0_r
                        return (
                            pat0_conj,
                            self.absurd3(actual_pat0_r, pat1_l),
                            self.absurd4(pat0_l, pat1),
                        )
                    else:
                        pat0_conj.negated = True
                        assert pat0_r is not None
                        actual_pat0_r = pat0_r
                        return (
                            pat0_conj,
                            self.imim(actual_pat0_r, pat1_l),
                            self.absurd2(pat0_l, pat1),
                        )
            pat0_conj, pat0_l, pat0_r = self.to_conj(pat0)
            if isinstance(pat0_conj, ConjBool):
                if pat0_conj.negated:
                    assert pat1_r is not None
                    actual_pat1_r: ProofThunk = pat1_r
                    return pat1_conj, self.helper1(pat0_l, pat1_l), self.a1d(actual_pat1_r, pat0)
                else:
                    pf = self.absurd_i(pat0_l, pat1)
                    return ConjBool(True), pf, None
            assert pat0_r is not None
            actual_pat0_r = pat0_r
            assert pat1_r is not None
            actual_pat1_r = pat1_r
            if pat0_conj.negated:
                pat0_conj.negated = False
                return (
                    ConjOr(pat0_conj, pat1_conj),
                    self.imim(actual_pat0_r, pat1_l),
                    self.imim(pat0_l, actual_pat1_r),
                )
            else:
                pat0_conj.negated = True
                return (
                    ConjOr(pat0_conj, pat1_conj),
                    self.imim_nnr(actual_pat0_r, pat1_l),
                    self.imim_nnl(pat0_l, actual_pat1_r),
                )
        else:
            raise AssertionError(f'Unexpected pattern! Expected a propositional pattern but got:\n{str(pat)}\n')
