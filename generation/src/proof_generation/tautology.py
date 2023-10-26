from __future__ import annotations

from functools import partial
from typing import TYPE_CHECKING

from proof_generation.pattern import Implies, MetaVar, Notation, match_single
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
    from collections.abc import Callable

    from proof_generation.pattern import Pattern
    from proof_generation.proof import ProvedExpression
    from proof_generation.proved import Proved


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
            Implies(Implies(phi0, phi1), Implies(Implies(phi1, phi2), Implies(phi0, phi2))),
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

    def imp_trans_match1(self, h1: ProvedExpression, h2: ProvedExpression) -> Proved:
        """Same as imp_transitivity but h1 is instantiated to match h2"""
        h1_conc = self.PROVISIONAL_get_conc(h1)
        h2_conc = self.PROVISIONAL_get_conc(h2)
        _, b = Implies.extract(h1_conc)
        c, _ = Implies.extract(h2_conc)
        subst = match_single(b, c, {})
        assert subst is not None
        actual_subst: dict[int, Pattern] = subst
        return self.imp_transitivity(lambda: self.dynamic_inst(h1, actual_subst), h2)

    def imp_trans_match2(self, h1: ProvedExpression, h2: ProvedExpression) -> Proved:
        """Same as imp_transitivity but h2 is instantiated to match h1"""
        h1_conc = self.PROVISIONAL_get_conc(h1)
        h2_conc = self.PROVISIONAL_get_conc(h2)
        _, b = Implies.extract(h1_conc)
        c, _ = Implies.extract(h2_conc)
        subst = match_single(c, b, {})
        assert subst is not None
        actual_subst: dict[int, Pattern] = subst
        return self.imp_transitivity(h1, lambda: self.dynamic_inst(h2, actual_subst))

    def mpcom(self, p_pf: ProvedExpression, q: Pattern) -> Proved:
        """
               p
        -----------------
          (p -> q) -> q
        """
        p = self.PROVISIONAL_get_conc(p_pf)
        pq = Implies(p, q)
        return self.modus_ponens(
            self.modus_ponens(self.dynamic_inst(self.prop2, {0: pq, 1: p, 2: q}), self.imp_refl(pq)),
            self.imp_provable(pq, p_pf),
        )

    def imp_trans(self, p: Pattern = phi0, q: Pattern = phi1, r: Pattern = phi2) -> Proved:
        """(p -> q) -> (q -> r) -> p -> r"""
        return self.dynamic_inst(lambda: self.load_axiom(self.axioms()[0]), {0: p, 1: q, 2: r})

    def dni_l(self, p: Pattern, q: Pattern) -> Proved:
        """(p -> q) -> (~~p -> q)"""
        return self.modus_ponens(self.imp_trans(neg(neg(p)), p, q), self.dynamic_inst(self.prop3, {0: p}))

    def dni_l_i(self, pq: ProvedExpression) -> Proved:
        """
            p -> q
        --------------
          ~~p -> q
        """
        pq_conc = self.PROVISIONAL_get_conc(pq)
        p, q = Implies.extract(pq_conc)
        return self.modus_ponens(self.dni_l(p, q), pq())

    def dni_r(self, p: Pattern, q: Pattern) -> Proved:
        """(p -> q) -> (p -> ~~q)"""
        return self.modus_ponens(
            self.dynamic_inst(self.prop2, {0: p, 1: q, 2: neg(neg(q))}),
            self.imp_provable(p, lambda: self.dneg_intro(q)),
        )

    def dni_r_i(self, pq: ProvedExpression) -> Proved:
        """
           p -> q
        --------------
          p -> ~~q
        """
        pq_conc = self.PROVISIONAL_get_conc(pq)
        p, q = Implies.extract(pq_conc)
        return self.modus_ponens(self.dni_r(p, q), pq())

    def dne_l(self, p: Pattern, q: Pattern) -> Proved:
        """(~~p -> q) -> (p -> q)"""
        return self.modus_ponens(self.imp_trans(p, neg(neg(p)), q), self.dneg_intro(p))

    def dne_l_i(self, pq: ProvedExpression) -> Proved:
        """
          ~~p -> q
        --------------
            p -> q
        """
        pq_conc = self.PROVISIONAL_get_conc(pq)
        p, q = Implies.extract(pq_conc)
        return self.modus_ponens(self.dne_l(p, q), pq())

    def dne_r(self, p: Pattern, q: Pattern) -> Proved:
        """(p -> ~~q) -> (p -> q)"""
        return self.modus_ponens(
            self.dynamic_inst(self.prop2, {0: p, 1: neg(neg(q)), 2: q}),
            self.imp_provable(p, lambda: self.dynamic_inst(self.prop3, {0: q})),
        )

    def dne_r_i(self, pq: ProvedExpression) -> Proved:
        """
          p -> ~~q
        --------------
           p -> q
        """
        pq_conc = self.PROVISIONAL_get_conc(pq)
        p, q = Implies.extract(pq_conc)
        return self.modus_ponens(self.dne_r(p, q), pq())

    def helper1(self, p_pf: ProvedExpression, qr_pf: ProvedExpression) -> Proved:
        """
           p    q -> r
        -----------------
          (p -> q) -> r
        """
        qr = self.PROVISIONAL_get_conc(qr_pf)
        q, r = Implies.extract(qr)
        return self.imp_transitivity(lambda: self.mpcom(p_pf, q), qr_pf)

    def a1d(self, pq: ProvedExpression, r: Pattern) -> Proved:
        """
             p -> q
        ---------------
          p -> r -> q
        """
        pq_conc = self.PROVISIONAL_get_conc(pq)
        p, q = Implies.extract(pq_conc)
        return self.imp_transitivity(pq, lambda: self.dynamic_inst(self.prop1, {0: q, 1: r}))

    def con3(self, p: Pattern, q: Pattern) -> Proved:
        """(p -> q) -> (~q -> ~p)"""
        return self.imp_trans(p, q, bot)

    def con3_i(self, pq: ProvedExpression) -> Proved:
        """
          p -> q
        ------------
          ~q -> ~p
        """
        pq_conc = self.PROVISIONAL_get_conc(pq)
        p, q = Implies.extract(pq_conc)
        return self.modus_ponens(self.con3(p, q), pq())

    def absurd2(self, pq: ProvedExpression, r: Pattern) -> Proved:
        """
             p -> q
        -----------------
           ~q -> p -> r
        """
        pq_conc = self.PROVISIONAL_get_conc(pq)
        p, q = Implies.extract(pq_conc)
        return self.imp_transitivity(
            lambda: self.absurd(q, r), lambda: self.modus_ponens(self.imp_trans(p, q, r), pq())
        )

    def lemma1(self, q: Pattern, pf: ProvedExpression) -> Proved:
        """
                ~p
        ------------------
          (q -> p) -> ~q
        """
        np = self.PROVISIONAL_get_conc(pf)
        p = Negation.extract(np)[0]
        return self.modus_ponens(self.dynamic_inst(self.prop2, {0: q, 1: p, 2: bot}), self.imp_provable(q, pf))

    def con1(self, pf: ProvedExpression) -> Proved:
        """
          ~p -> q
        -----------
          ~q -> p
        """
        npq = self.PROVISIONAL_get_conc(pf)
        np, q = Implies.extract(npq)
        p = Negation.extract(np)[0]
        return self.imp_transitivity(
            lambda: self.modus_ponens(
                self.ant_commutativity(
                    lambda: self.imp_transitivity(
                        lambda: self.dynamic_inst(self.prop1, {0: neg(q), 1: np}),
                        lambda: self.dynamic_inst(self.prop2, {0: np, 1: q, 2: bot}),
                    )
                ),
                pf(),
            ),
            lambda: self.dynamic_inst(self.prop3, {0: p}),
        )

    def absurd3(self, npq_pf: ProvedExpression, nr_pf: ProvedExpression) -> Proved:
        """
           ~p -> q     ~r
        -------------------
           (q -> r) -> p
        """
        npq = self.PROVISIONAL_get_conc(npq_pf)
        nr = self.PROVISIONAL_get_conc(nr_pf)
        np, q = Implies.extract(npq)
        Negation.extract(np)[0]
        Negation.extract(nr)[0]
        return self.imp_transitivity(lambda: self.lemma1(q, nr_pf), lambda: self.con1(npq_pf))

    def absurd4(self, pnq_pf: ProvedExpression, r: Pattern) -> Proved:
        """
           p -> ~q
        ------------------
           q -> p -> r
        """
        pnq = self.PROVISIONAL_get_conc(pnq_pf)
        p, nq = Implies.extract(pnq)
        q = Negation.extract(nq)[0]
        return self.imp_transitivity(lambda: self.dneg_intro(q), lambda: self.absurd2(pnq_pf, r))

    def absurd_i(self, np_pf: ProvedExpression, q: Pattern) -> Proved:
        """
           ~p
        -----------
          p -> q
        """
        np = self.PROVISIONAL_get_conc(np_pf)
        p = Negation.extract(np)[0]
        return self.modus_ponens(self.absurd(p, q), np_pf())

    def and_not_r_intro(self, p_pf: ProvedExpression, nq_pf: ProvedExpression) -> Proved:
        """
           p   ~q
        -------------
          ~(p -> q)
        """
        nq = self.PROVISIONAL_get_conc(nq_pf)
        q = Negation.extract(nq)[0]
        return self.imp_transitivity(lambda: self.mpcom(p_pf, q), nq_pf)

    def imim_l(self, pat: Pattern, h: ProvedExpression) -> Proved:
        """
              a -> b
        ---------------------
        (b -> c) -> (a -> c)
        """
        ab = self.PROVISIONAL_get_conc(h)
        a, b = Implies.extract(ab)
        return self.modus_ponens(self.imp_trans(a, b, pat), h())

    def imim(self, h1: ProvedExpression, h2: ProvedExpression) -> Proved:
        """
        (a -> b)    (c -> d)
        ---------------------
        (b -> c) -> (a -> d)
        """
        h1_conc = self.PROVISIONAL_get_conc(h1)
        h2_conc = self.PROVISIONAL_get_conc(h2)
        a, b = Implies.extract(h1_conc)
        c, d = Implies.extract(h2_conc)
        return self.imp_transitivity(
            lambda: self.imim_l(c, h1),
            lambda: self.modus_ponens(self.dynamic_inst(self.prop2, {0: a, 1: c, 2: d}), self.imp_provable(a, h2)),
        )

    def imim_r(self, pat: Pattern, h: ProvedExpression) -> Proved:
        """
              a -> b
        ---------------------
        (c -> a) -> (c -> b)
        """
        return self.imim(lambda: self.imp_refl(pat), h)

    def imim_nnr(self, h1: ProvedExpression, h2: ProvedExpression) -> Proved:
        """
        (a -> b)    (c -> d)
        ---------------------
        (b -> c) -> (~~a -> d)
        """
        h1_conc = self.PROVISIONAL_get_conc(h1)
        h2_conc = self.PROVISIONAL_get_conc(h2)
        a, b = Implies.extract(h1_conc)
        c, d = Implies.extract(h2_conc)
        return self.imp_transitivity(
            lambda: self.imim(h1, h2),
            lambda: self.modus_ponens(self.imp_trans(neg(neg(a)), a, d), self.dynamic_inst(self.prop3, {0: a})),
        )

    def imim_nnl(self, h1: ProvedExpression, h2: ProvedExpression) -> Proved:
        """
        (a -> b)    (c -> d)
        ---------------------
        (~~b -> c) -> (a -> d)
        """
        h1_conc = self.PROVISIONAL_get_conc(h1)
        h2_conc = self.PROVISIONAL_get_conc(h2)
        a, b = Implies.extract(h1_conc)
        c, d = Implies.extract(h2_conc)
        return self.imp_transitivity(
            lambda: self.modus_ponens(self.imp_trans(b, neg(neg(b)), c), self.dneg_intro(b)), lambda: self.imim(h1, h2)
        )

    def imim_or(self, h1: ProvedExpression, h2: ProvedExpression) -> Proved:
        """
        (a -> b)   (c -> d)
        ---------------------
        a \\/ c -> b \\/ d
        """
        return self.imim(lambda: self.con3_i(h1), h2)

    def imim_and(self, h1: ProvedExpression, h2: ProvedExpression) -> Proved:
        """
        (a -> b)   (c -> d)
        ---------------------
        a /\\ c -> b /\\ d
        """
        return self.con3_i(lambda: self.imim(h1, lambda: self.con3_i(h2)))

    def imim_and_r(self, pat: Pattern, h: ProvedExpression) -> Proved:
        """
           (b -> c)
        ---------------------
           a /\\ b -> a /\\ c
        """
        return self.imim_and(lambda: self.imp_refl(pat), h)

    def imim_and_l(self, pat: Pattern, h: ProvedExpression) -> Proved:
        """
            (a -> b)
        ---------------------
           a /\\ c -> b /\\ c
        """
        return self.imim_and(h, lambda: self.imp_refl(pat))

    def imim_or_r(self, pat: Pattern, h: ProvedExpression) -> Proved:
        """
             (b -> c)
        ---------------------
            a \\/ b -> a \\/ c
        """
        return self.imim(lambda: self.imp_refl(neg(pat)), h)

    def imim_or_l(self, pat: Pattern, h: ProvedExpression) -> Proved:
        """
              (a -> b)
        ---------------------
           a \\/ c -> b \\/ c
        """
        return self.imim(lambda: self.con3_i(h), lambda: self.imp_refl(pat))

    def and_intro(self, p_pf: ProvedExpression, q_pf: ProvedExpression) -> Proved:
        """
            p   q
        ------------
           p /\\ q
        """
        self.PROVISIONAL_get_conc(p_pf)
        q = self.PROVISIONAL_get_conc(q_pf)
        return self.imp_transitivity(
            lambda: self.mpcom(p_pf, neg(q)), lambda: self.modus_ponens(self.dneg_intro(q), q_pf())
        )

    def and_assoc_r(self, pat1: Pattern = phi0, pat2: Pattern = phi1, pat3: Pattern = phi2) -> Proved:
        """(a /\\ b) /\\ c -> a /\\ (b /\\ c)"""
        return self.dynamic_inst(lambda: self.load_axiom(self.axioms()[1]), {0: pat1, 1: pat2, 2: pat3})

    def and_assoc_l(self, pat1: Pattern = phi0, pat2: Pattern = phi1, pat3: Pattern = phi2) -> Proved:
        """a /\\ (b /\\ c) -> (a /\\ b) /\\ c"""
        return self.dynamic_inst(lambda: self.load_axiom(self.axioms()[2]), {0: pat1, 1: pat2, 2: pat3})

    def or_assoc_r(self, pat1: Pattern = phi0, pat2: Pattern = phi1, pat3: Pattern = phi2) -> Proved:
        """(a \\/ b) \\/ c -> a \\/ (b \\/ c)"""
        return self.dynamic_inst(lambda: self.load_axiom(self.axioms()[3]), {0: pat1, 1: pat2, 2: pat3})

    def or_assoc_l(self, pat1: Pattern = phi0, pat2: Pattern = phi1, pat3: Pattern = phi2) -> Proved:
        """a \\/ (b \\/ c) -> (a \\/ b) \\/ c"""
        return self.dynamic_inst(lambda: self.load_axiom(self.axioms()[4]), {0: pat1, 1: pat2, 2: pat3})

    def or_distr_r(self, pat1: Pattern = phi0, pat2: Pattern = phi1, pat3: Pattern = phi2) -> Proved:
        """(a /\\ b) \\/ c -> (a \\/ c) /\\ (b \\/ c)"""
        return self.dynamic_inst(lambda: self.load_axiom(self.axioms()[5]), {0: pat1, 1: pat2, 2: pat3})

    def or_distr_r_rev(self, pat1: Pattern = phi0, pat2: Pattern = phi1, pat3: Pattern = phi2) -> Proved:
        """(a \\/ c) /\\ (b \\/ c) -> (a /\\ b) \\/ c"""
        return self.dynamic_inst(lambda: self.load_axiom(self.axioms()[6]), {0: pat1, 1: pat2, 2: pat3})

    def or_distr_l(self, pat1: Pattern = phi0, pat2: Pattern = phi1, pat3: Pattern = phi2) -> Proved:
        """a \\/ (b /\\ c) -> (a \\/ b) /\\ (a \\/ c)"""
        return self.dynamic_inst(lambda: self.load_axiom(self.axioms()[7]), {0: pat1, 1: pat2, 2: pat3})

    def or_distr_l_rev(self, pat1: Pattern = phi0, pat2: Pattern = phi1, pat3: Pattern = phi2) -> Proved:
        """(a \\/ b) /\\ (a \\/ c) -> a \\/ (b /\\ c)"""
        return self.dynamic_inst(lambda: self.load_axiom(self.axioms()[8]), {0: pat1, 1: pat2, 2: pat3})

    def and_assoc(self, pat1: Pattern = phi0, pat2: Pattern = phi1, pat3: Pattern = phi2) -> Proved:
        """a /\\ (b /\\ c) <-> (a /\\ b) /\\ c"""
        return self.and_intro(
            (lambda: self.and_assoc_l(pat1, pat2, pat3)), (lambda: self.and_assoc_r(pat1, pat2, pat3))
        )

    def or_assoc(self, pat1: Pattern = phi0, pat2: Pattern = phi1, pat3: Pattern = phi2) -> Proved:
        """a \\/ (b \\/ c) <-> (a \\/ b) \\/ c"""
        return self.and_intro((lambda: self.or_assoc_l(pat1, pat2, pat3)), (lambda: self.or_assoc_r(pat1, pat2, pat3)))

    def and_comm(self, p: Pattern = phi0, q: Pattern = phi1) -> Proved:
        """p /\\ q <-> q /\\ p"""
        return self.dynamic_inst(lambda: self.load_axiom(self.axioms()[9]), {0: p, 1: q})

    def or_comm_imp(self, p: Pattern = phi0, q: Pattern = phi1) -> Proved:
        """p \\/ q -> q \\/ p"""
        return self.imp_transitivity(lambda: self.imp_trans(neg(p), q, bot), lambda: self.dne_r(neg(q), p))

    def or_comm(self, p: Pattern = phi0, q: Pattern = phi1) -> Proved:
        """p \\/ q <-> q \\/ p"""
        return self.and_intro(lambda: self.or_comm_imp(p, q), lambda: self.or_comm_imp(q, p))

    def and_l_imp(self, p: Pattern = phi0, q: Pattern = phi1) -> Proved:
        """p /\\ q -> p"""
        return self.con1(lambda: self.absurd(p, neg(q)))

    def and_l(self, pq_pf: ProvedExpression) -> Proved:
        """
           p /\\ q
        ------------
              p
        """
        p, q = And.extract(self.PROVISIONAL_get_conc(pq_pf))
        return self.modus_ponens(self.and_l_imp(p, q), pq_pf())

    def and_r_imp(self, p: Pattern = phi0, q: Pattern = phi1) -> Proved:
        """p /\\ q -> q"""
        return self.con1(lambda: self.dynamic_inst(self.prop1, {0: neg(q), 1: p}))

    def and_r(self, pq_pf: ProvedExpression) -> Proved:
        """
           p /\\ q
        ------------
              q
        """
        p, q = And.extract(self.PROVISIONAL_get_conc(pq_pf))
        return self.modus_ponens(self.and_r_imp(p, q), pq_pf())

    def equiv_refl(self, p: Pattern = phi0) -> Proved:
        """p <-> p"""
        pf = lambda: self.imp_refl(p)
        return self.and_intro(pf, pf)

    def equiv_sym(self, pf: ProvedExpression) -> Proved:
        """
          p <-> q
        -----------
          q <-> p
        """
        return self.and_intro(lambda: self.and_r(pf), lambda: self.and_l(pf))

    def equiv_transitivity(self, pq_pf: ProvedExpression, qr_pf: ProvedExpression) -> Proved:
        """
           p <-> q    q <-> r
        ----------------------
                p <-> r
        """
        return self.and_intro(
            lambda: self.imp_transitivity(lambda: self.and_l(pq_pf), lambda: self.and_l(qr_pf)),
            lambda: self.imp_transitivity(lambda: self.and_r(qr_pf), lambda: self.and_r(pq_pf)),
        )

    def equiv_trans_match1(self, h1: ProvedExpression, h2: ProvedExpression) -> Proved:
        """Same as equiv_transitivity but h1 is instantiated to match h2"""
        h1_conc = self.PROVISIONAL_get_conc(h1)
        h2_conc = self.PROVISIONAL_get_conc(h2)
        _, b = Equiv.extract(h1_conc)
        c, _ = Equiv.extract(h2_conc)
        subst = match_single(b, c, {})
        assert subst is not None
        actual_subst: dict[int, Pattern] = subst
        return self.equiv_transitivity(lambda: self.dynamic_inst(h1, actual_subst), h2)

    def equiv_trans_match2(self, h1: ProvedExpression, h2: ProvedExpression) -> Proved:
        """Same as equiv_transitivity but h2 is instantiated to match h1"""
        h1_conc = self.PROVISIONAL_get_conc(h1)
        h2_conc = self.PROVISIONAL_get_conc(h2)
        _, b = Equiv.extract(h1_conc)
        c, _ = Equiv.extract(h2_conc)
        subst = match_single(c, b, {})
        assert subst is not None
        actual_subst: dict[int, Pattern] = subst
        return self.equiv_transitivity(h1, lambda: self.dynamic_inst(h2, actual_subst))

    def and_cong(self, pf1: ProvedExpression, pf2: ProvedExpression) -> Proved:
        return self.and_intro(
            (lambda: self.imim_and((lambda: self.and_l(pf1)), (lambda: self.and_l(pf2)))),
            (lambda: self.imim_and((lambda: self.and_r(pf1)), (lambda: self.and_r(pf2)))),
        )

    def or_cong(self, pf1: ProvedExpression, pf2: ProvedExpression) -> Proved:
        return self.and_intro(
            (lambda: self.imim_or((lambda: self.and_l(pf1)), (lambda: self.and_l(pf2)))),
            (lambda: self.imim_or((lambda: self.and_r(pf1)), (lambda: self.and_r(pf2)))),
        )

    def resolution(self, p: Pattern = phi0, a: Pattern = phi1, b: Pattern = phi2) -> Proved:
        """~p \\/ a -> p \\/ b -> a \\/ b"""
        return self.imp_transitivity(lambda: self.or_comm_imp(neg(p), a), lambda: self.imp_trans(neg(a), neg(p), b))

    def resolution_r(self, p: Pattern = phi0, b: Pattern = phi1) -> Proved:
        """~p -> p \\/ b -> b"""
        return self.ant_commutativity(lambda: self.imp_refl(Or(p, b)))

    def resolution_l(self, p: Pattern = phi0, a: Pattern = phi1) -> Proved:
        """~p \\/ a -> p -> a"""
        return self.imim_l(a, lambda: self.dneg_intro(p))

    def resolution_base(self, p: Pattern = phi0) -> Proved:
        """~p -> p -> bot"""
        return self.imp_refl(neg(p))

    def resolution_step(self, ab_pf: ProvedExpression, ac_pf: ProvedExpression, bcd_pf: ProvedExpression) -> Proved:
        """
          a -> b    a -> c    b -> c -> d
        -----------------------------------
                      a -> d
        """
        ab = self.PROVISIONAL_get_conc(ab_pf)
        a, b = Implies.extract(ab)
        ac = self.PROVISIONAL_get_conc(ac_pf)
        a2, c = Implies.extract(ac)
        assert a == a2
        bcd = self.PROVISIONAL_get_conc(bcd_pf)
        b2, cd = Implies.extract(bcd)
        assert b == b2
        c2, d = Implies.extract(cd)
        assert c == c2
        return self.modus_ponens(
            self.modus_ponens(self.dynamic_inst(self.prop2, {0: a, 1: c, 2: d}), self.imp_transitivity(ab_pf, bcd_pf)),
            ac_pf(),
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

    def to_conj(self, pat: Pattern) -> tuple[ConjTerm, ProvedExpression, ProvedExpression | None]:
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
            return ConjBool(False), self.top_intro, None
        if pat == top:
            return ConjBool(True), self.top_intro, None
        if isinstance(pat, MetaVar):
            phi_imp_phi = lambda: self.imp_refl(pat)
            return ConjVar(pat.name), phi_imp_phi, phi_imp_phi
        elif pat_imp := Implies.extract(pat):
            pat0 = pat_imp[0]
            pat1 = pat_imp[1]
            pat1_conj, pat1_l, pat1_r = self.to_conj(pat1)

            if isinstance(pat1_conj, ConjBool):
                if pat1_conj.negated:
                    pf = lambda: self.imp_provable(pat0, pat1_l)
                    return ConjBool(True), pf, None
                else:
                    pat0_conj, pat0_l, pat0_r = self.to_conj(pat0)
                    if isinstance(pat0_conj, ConjBool):
                        if pat0_conj.negated:
                            pf = lambda: self.and_not_r_intro(pat0_l, pat1_l)
                            return ConjBool(False), pf, None
                        else:
                            pf = lambda: self.absurd_i(pat0_l, pat1)
                            return ConjBool(True), pf, None
                    if pat0_conj.negated:
                        pat0_conj.negated = False
                        assert pat0_r is not None
                        actual_pat0_r: ProvedExpression = pat0_r
                        return (
                            pat0_conj,
                            (lambda: self.absurd3(actual_pat0_r, pat1_l)),
                            (lambda: self.absurd4(pat0_l, pat1)),
                        )
                    else:
                        pat0_conj.negated = True
                        assert pat0_r is not None
                        actual_pat0_r = pat0_r
                        return (
                            pat0_conj,
                            (lambda: self.imim(actual_pat0_r, pat1_l)),
                            (lambda: self.absurd2(pat0_l, pat1)),
                        )
            pat0_conj, pat0_l, pat0_r = self.to_conj(pat0)
            if isinstance(pat0_conj, ConjBool):
                if pat0_conj.negated:
                    assert pat1_r is not None
                    actual_pat1_r: ProvedExpression = pat1_r
                    return pat1_conj, (lambda: self.helper1(pat0_l, pat1_l)), (lambda: self.a1d(actual_pat1_r, pat0))
                else:
                    pf = lambda: self.absurd_i(pat0_l, pat1)
                    return ConjBool(True), pf, None
            assert pat0_r is not None
            actual_pat0_r = pat0_r
            assert pat1_r is not None
            actual_pat1_r = pat1_r
            if pat0_conj.negated:
                pat0_conj.negated = False
                return (
                    ConjOr(pat0_conj, pat1_conj),
                    (lambda: self.imim(actual_pat0_r, pat1_l)),
                    (lambda: self.imim(pat0_l, actual_pat1_r)),
                )
            else:
                pat0_conj.negated = True
                return (
                    ConjOr(pat0_conj, pat1_conj),
                    (lambda: self.imim_nnr(actual_pat0_r, pat1_l)),
                    (lambda: self.imim_nnl(pat0_l, actual_pat1_r)),
                )
        else:
            raise AssertionError(f'Unexpected pattern! Expected a propositional pattern but got:\n{str(pat)}\n')

    def propag_neg(self, term: ConjTerm) -> tuple[ConjTerm, ProvedExpression, ProvedExpression]:
        """Assumes `term` is made up only of OR nodes and vars (+ single negations)"""
        if isinstance(term, ConjVar):
            pat: Pattern = MetaVar(term.id)
            if term.negated:
                pat = neg(pat)
            phi_imp_phi = lambda: self.imp_refl(pat)
            return term, phi_imp_phi, phi_imp_phi
        elif isinstance(term, ConjOr):
            if term.negated:
                term.left.negated = not term.left.negated
                term.right.negated = not term.right.negated
                term_l, term_l_pf1, term_l_pf2 = self.propag_neg(term.left)
                term_r, term_r_pf1, term_r_pf2 = self.propag_neg(term.right)
                if not term.left.negated:
                    term_l_pf1 = partial(self.dni_l_i, term_l_pf1)
                    term_l_pf2 = partial(self.dni_r_i, term_l_pf2)
                pf1 = lambda: self.imim_and(term_l_pf1, term_r_pf1)
                pf2 = lambda: self.imim_and(term_l_pf2, term_r_pf2)
                if term.right.negated:
                    pf1_conc = self.PROVISIONAL_get_conc(pf1)
                    pf1_l, pf1_r = Implies.extract(pf1_conc)
                    a1, nb1 = And.extract(pf1_l)
                    b1 = Negation.extract(nb1)[0]
                    pf1 = partial(self.imp_transitivity, partial(self.con3_i, partial(self.dne_r, a1, b1)), pf1)
                    pf2_conc = self.PROVISIONAL_get_conc(pf2)
                    pf2_l, pf2_r = Implies.extract(pf2_conc)
                    a2, nb2 = And.extract(pf2_r)
                    b2 = Negation.extract(nb2)[0]
                    pf2 = partial(self.imp_transitivity, pf2, partial(self.con3_i, partial(self.dni_r, a2, b2)))
                return ConjAnd(term_l, term_r), pf1, pf2
            else:
                term_l, term_l_pf1, term_l_pf2 = self.propag_neg(term.left)
                term_r, term_r_pf1, term_r_pf2 = self.propag_neg(term.right)
                return (
                    ConjOr(term_l, term_r),
                    (lambda: self.imim_or(term_l_pf1, term_r_pf1)),
                    (lambda: self.imim_or(term_l_pf2, term_r_pf2)),
                )
        else:
            raise AssertionError(
                f'Unexpected pattern! Expected a term with only Or, And and Not but got:\n{str(term)}\n'
            )

    def to_cnf(self, term: ConjTerm) -> tuple[ConjTerm, ProvedExpression, ProvedExpression]:
        """Assumes negation has been fully propagated through the term"""
        if isinstance(term, ConjVar):
            pat: Pattern = MetaVar(term.id)
            if term.negated:
                pat = neg(pat)
            phi_imp_phi = lambda: self.imp_refl(pat)
            return term, phi_imp_phi, phi_imp_phi
        elif isinstance(term, ConjAnd):
            term_l, term_l_pf1, term_l_pf2 = self.to_cnf(term.left)
            term_r, term_r_pf1, term_r_pf2 = self.to_cnf(term.right)
            pf1 = lambda: self.imim_and(term_l_pf1, term_r_pf1)
            pf2 = lambda: self.imim_and(term_l_pf2, term_r_pf2)
            return ConjAnd(term_l, term_r), pf1, pf2
        elif isinstance(term, ConjOr):
            term_l, term_l_pf1, term_l_pf2 = self.to_cnf(term.left)
            term_r, term_r_pf1, term_r_pf2 = self.to_cnf(term.right)
            pf1 = lambda: self.imim_or(term_l_pf1, term_r_pf1)
            pf2 = lambda: self.imim_or(term_l_pf2, term_r_pf2)
            pf1_conc = self.PROVISIONAL_get_conc(pf1)
            Implies.extract(pf1_conc)
            if isinstance(term_l, ConjAnd):
                pf1 = partial(self.imp_trans_match2, pf1, self.or_distr_r)
                pf2 = partial(self.imp_trans_match1, self.or_distr_r_rev, pf2)
                new_term, pf1_, pf2_ = self.to_cnf(ConjAnd(ConjOr(term_l.left, term_r), ConjOr(term_l.right, term_r)))
                pf1 = partial(self.imp_transitivity, pf1, pf1_)
                pf2 = partial(self.imp_transitivity, pf2_, pf2)
                return new_term, pf1, pf2
            elif isinstance(term_r, ConjAnd):
                pf1 = partial(self.imp_trans_match2, pf1, self.or_distr_l)
                pf2 = partial(self.imp_trans_match1, self.or_distr_l_rev, pf2)
                new_term, pf1_, pf2_ = self.to_cnf(ConjAnd(ConjOr(term_l, term_r.left), ConjOr(term_l, term_r.right)))
                pf1 = partial(self.imp_transitivity, pf1, pf1_)
                pf2 = partial(self.imp_transitivity, pf2_, pf2)
                return new_term, pf1, pf2
            else:
                return ConjOr(term_l, term_r), pf1, pf2
        else:
            raise AssertionError(f'Unexpected pattern! Expected a term with only Or and And but got:\n{str(term)}\n')

    def to_clauses(self, term: ConjTerm) -> tuple[list[list[int]], ProvedExpression, ProvedExpression]:
        """Assumes term is in CNF form"""
        if isinstance(term, ConjVar):
            if term.negated:
                id = -(term.id + 1)
            else:
                id = term.id + 1
            pat: Pattern = MetaVar(term.id)
            if term.negated:
                pat = neg(pat)
            phi_imp_phi = lambda: self.imp_refl(pat)
            return [[id]], phi_imp_phi, phi_imp_phi
        elif isinstance(term, ConjAnd):
            term_l, term_l_pf1, term_l_pf2 = self.to_clauses(term.left)
            term_r, term_r_pf1, term_r_pf2 = self.to_clauses(term.right)
            pf1 = lambda: self.imim_and(term_l_pf1, term_r_pf1)
            pf2 = lambda: self.imim_and(term_l_pf2, term_r_pf2)
            l = len(term_l)
            assert l > 0
            if l > 1:
                shift_right: ProvedExpression = self.and_assoc_r
                shift_left: ProvedExpression = self.and_assoc_l
                for i in range(0, l - 2):
                    shift_right = partial(
                        lambda i, shift_right: self.imp_trans_match1(
                            self.and_assoc_r,
                            partial(self.imim_and_r, MetaVar(i + 3), shift_right),
                        ),
                        i,
                        shift_right,
                    )
                    shift_left = partial(
                        lambda i, shift_left: self.imp_trans_match2(
                            partial(self.imim_and_r, MetaVar(i + 3), shift_left),
                            self.and_assoc_l,
                        ),
                        i,
                        shift_left,
                    )
                pf1 = partial(self.imp_trans_match2, pf1, shift_right)
                pf2 = partial(self.imp_trans_match1, shift_left, pf2)
            return term_l + term_r, pf1, pf2
        elif isinstance(term, ConjOr):
            term_l, term_l_pf1, term_l_pf2 = self.to_clauses(term.left)
            term_r, term_r_pf1, term_r_pf2 = self.to_clauses(term.right)
            pf1 = lambda: self.imim_or(term_l_pf1, term_r_pf1)
            pf2 = lambda: self.imim_or(term_l_pf2, term_r_pf2)
            assert len(term_l) == 1
            assert len(term_r) == 1
            l = len(term_l[0])
            assert l > 0
            if l > 1:
                shift_right = self.or_assoc_r
                shift_left = self.or_assoc_l
                for i in range(0, l - 2):
                    shift_right = partial(
                        lambda i, shift_right: self.imp_trans_match1(
                            self.or_assoc_r,
                            partial(self.imim_or_r, MetaVar(i + 3), shift_right),
                        ),
                        i,
                        shift_right,
                    )
                    shift_left = partial(
                        lambda i, shift_left: self.imp_trans_match2(
                            partial(self.imim_or_r, MetaVar(i + 3), shift_left),
                            self.or_assoc_l,
                        ),
                        i,
                        shift_left,
                    )
                pf1 = partial(self.imp_trans_match2, pf1, shift_right)
                pf2 = partial(self.imp_trans_match1, shift_left, pf2)
            return [term_l[0] + term_r[0]], pf1, pf2
        else:
            raise AssertionError(
                f'Unexpected pattern! Expected a term with only Or, And and Negations but got:\n{str(term)}\n'
            )

    def AC_move_to_front(  # noqa: N802
        self,
        pos: int,
        len: int,
        assoc: ProvedExpression,
        comm: ProvedExpression,
        cong: Callable[[ProvedExpression, ProvedExpression], Proved],
        op: Callable[[Pattern, Pattern], Pattern],
    ) -> Proved:
        """
        Produces a proof of
        p0 . (p1 . (p2 . (... px . (... . pn)))) <-> px . (p0 . (p1 . (... px-1 . (px+1 . (... . pn)))))

        assoc is of the form: phi0 . (phi1 . phi2) <-> (phi0 . phi1) . phi2
        comm is of the form: phi0 . phi1 <-> phi1 . phi0
        cong is of the form:
            p <-> q   r <-> s
          ---------------------
            p . r <-> q . s
        """
        if pos == 0:
            return self.equiv_refl()
        assoc_rev = lambda: self.equiv_sym(assoc)
        is_last: bool = pos == len - 1
        if is_last:
            if pos == 1:
                return comm()
            pos -= 1
        term: Pattern = MetaVar(pos + 1)
        for i in range(pos, 1, -1):
            term = op(MetaVar(i), term)
        shift_left = lambda: self.dynamic_inst(assoc, {2: term})
        for _ in range(pos - 1):
            shift_left = partial(self.equiv_trans_match2, shift_left, assoc)
        if is_last:
            pf: ProvedExpression = lambda: self.equiv_trans_match2(shift_left, comm)
        else:
            pf = lambda: self.equiv_trans_match2(shift_left, lambda: cong(comm, (lambda: self.equiv_refl(phi2))))
            pf = partial(self.equiv_trans_match2, pf, assoc_rev)
        if pos > 1:
            for_phi0: Pattern = MetaVar(0)
            for i in range(1, pos - 1):
                for_phi0 = op(for_phi0, MetaVar(i))
            if is_last:
                for_phi2 = MetaVar(pos)
            else:
                for_phi2 = MetaVar(pos + 1)
            shift_right = lambda: self.dynamic_inst(assoc_rev, {0: for_phi0, 1: MetaVar(pos - 1), 2: for_phi2})
            for _ in range(pos - 2):
                shift_right = partial(self.equiv_trans_match2, shift_right, assoc_rev)
            if is_last:
                left_term = MetaVar(pos + 1)
            else:
                left_term = MetaVar(pos)
            return self.equiv_transitivity(pf, lambda: cong((lambda: self.equiv_refl(left_term)), shift_right))
        return pf()

    def or_move_to_front(self, pos: int, len: int) -> Proved:
        return self.AC_move_to_front(pos, len, self.or_assoc, self.or_comm, self.or_cong, Or)

    def and_move_to_front(self, pos: int, len: int) -> Proved:
        return self.AC_move_to_front(pos, len, self.and_assoc, self.and_comm, self.and_cong, And)

    def reduce_duplicates_at_front(self, p: Pattern = phi0, q: Pattern = phi1) -> Proved:
        """p \\/ (p \\/ q) <-> p \\/ q"""
        return self.equiv_transitivity(
            lambda: self.or_assoc(p, p, q),
            lambda: self.and_intro(
                lambda: self.imim_or_l(q, lambda: self.dynamic_inst(self.peirce_bot, {0: p})),
                lambda: self.imim_or_l(q, lambda: self.dynamic_inst(self.prop1, {0: p, 1: neg(p)})),
            ),
        )

    def reduce_n_duplicates_at_front(self, n: int, p_id: int, q_id: int) -> Proved:
        """p \\/ (p  ... (p \\/ q)) <-> p \\/ q"""
        p = id_to_metavar(p_id)
        q = id_to_metavar(q_id)
        if n == 0:
            return self.equiv_refl(Or(p, q))
        pf = partial(self.reduce_duplicates_at_front, p, q)
        for i in range(1, n):
            pat = clause_to_pattern(([p_id] * i) + [q_id])
            pf = partial(self.equiv_transitivity, partial(self.reduce_duplicates_at_front, p, pat), pf)
        return pf()
