from __future__ import annotations

from typing import List

from proof_generation.matching import match_single
from proof_generation.pattern import Pattern, Implication, MetaVar, Bot, Notation
from proof_generation.proved import Proved
from proof_generation.proof import ProvedExpression
from proof_generation.proofs.propositional import Propositional, Negation, Top, Or, And, neg, bot, phi0, phi1, phi2


# Structure of Conjunctive Form Tree
class ConjTerm:
    negated: bool


class ConjAnd(ConjTerm):
    left: ConjTerm
    right: ConjTerm

    def __init__(self, left, right):
        self.left = left
        self.right = right
        self.negated = False


class ConjOr(ConjTerm):
    left: ConjTerm
    right: ConjTerm

    def __init__(self, left, right):
        self.left = left
        self.right = right
        self.negated = False


class ConjBool(ConjTerm):
    def __init__(self, negated):
        self.negated = negated


class ConjVar(ConjTerm):
    id: int

    def __init__(self, id):
        self.id = id
        self.negated = False


class Tautology(Propositional):

    def imp_trans_match1(self, h1: ProvedExpression, h2: ProvedExpression) -> Proved:
        h1_conc = self.PROVISIONAL_get_conc(h1)
        h2_conc = self.PROVISIONAL_get_conc(h2)
        _, b = Implication.extract(h1_conc)
        c, _ = Implication.extract(h2_conc)
        subst = match_single(b, c, {})
        assert subst is not None
        return self.imp_transitivity(lambda: self.dynamic_inst(h1, subst), h2)

    def imp_trans_match2(self, h1: ProvedExpression, h2: ProvedExpression) -> Proved:
        h1_conc = self.PROVISIONAL_get_conc(h1)
        h2_conc = self.PROVISIONAL_get_conc(h2)
        _, b = Implication.extract(h1_conc)
        c, _ = Implication.extract(h2_conc)
        subst = match_single(c, b, {})
        assert subst is not None
        return self.imp_transitivity(h1, lambda: self.dynamic_inst(h2, subst))

    #        p
    # -----------------
    #   (p -> q) -> q
    def mpcom(self, p_pf: ProvedExpression, q: Pattern) -> Proved:
        p = self.PROVISIONAL_get_conc(p_pf)
        pq = Implication(p, q)
        return self.modus_ponens(
            self.modus_ponens(
                self.dynamic_inst(self.prop2, {0: pq, 1: p, 2: q}),
                self.imp_refl(pq)),
            self.imp_provable(pq, p_pf))

    # (p -> q) -> (q -> r) -> p -> r
    def imp_trans(self, p: Pattern, q: Pattern, r: Pattern) -> Proved:
        # TODO
        return Proved(
            self.interpreter, Implication(Implication(p, q), Implication(Implication(q, r), Implication(p, r)))
        )

    # p -> ~~p
    def dni(self, p: Pattern) -> Proved:
        # TODO
        return Proved(self.interpreter, Implication(p, neg(neg(p))))

    def dni_l(self, p: Pattern, q: Pattern) -> Proved:
        return self.modus_ponens(
            self.imp_trans(neg(neg(p)), p, q),
            self.dynamic_inst(self.prop3, {0: p}))

    def dni_l_i(self, pq: ProvedExpression) -> Proved:
        pq_conc = self.PROVISIONAL_get_conc(pq)
        p, q = Implication.extract(pq_conc)
        return self.modus_ponens(self.dni_l(p, q), pq())

    def dni_r(self, p: Pattern, q: Pattern) -> Proved:
        return self.modus_ponens(
            self.dynamic_inst(self.prop2, {0: p, 1: q, 2: neg(neg(q))}),
            self.imp_provable(p, lambda: self.dni(q))
        )

    def dni_r_i(self, pq: ProvedExpression) -> Proved:
        pq_conc = self.PROVISIONAL_get_conc(pq)
        p, q = Implication.extract(pq_conc)
        return self.modus_ponens(self.dni_r(p, q), pq())

    def dne_l(self, p: Pattern, q: Pattern) -> Proved:
        return self.modus_ponens(
            self.imp_trans(p, neg(neg(p)), q),
            self.dni(p))

    def dne_l_i(self, pq: ProvedExpression) -> Proved:
        pq_conc = self.PROVISIONAL_get_conc(pq)
        p, q = Implication.extract(pq_conc)
        return self.modus_ponens(self.dne_l(p, q), pq())

    def dne_r(self, p: Pattern, q: Pattern) -> Proved:
        return self.modus_ponens(
            self.dynamic_inst(self.prop2, {0: p, 1: neg(neg(q)), 2: q}),
            self.imp_provable(p, lambda: self.dynamic_inst(self.prop3, {0: q})),
        )

    def dne_r_i(self, pq: ProvedExpression) -> Proved:
        pq_conc = self.PROVISIONAL_get_conc(pq)
        p, q = Implication.extract(pq_conc)
        return self.modus_ponens(self.dne_r(p, q), pq())

    #    p    q -> r
    # -----------------
    #   (p -> q) -> r
    def helper1(self, p_pf: ProvedExpression, qr_pf: ProvedExpression) -> Proved:
        qr = self.PROVISIONAL_get_conc(qr_pf)
        q, r = Implication.extract(qr)
        return self.imp_transitivity(self.mpcom(p_pf, q), qr_pf)

    #     p -> q
    # ---------------
    #   p -> r -> q
    def a1d(self, pq: ProvedExpression, r: Pattern) -> Proved:
        pq_conc = self.PROVISIONAL_get_conc(pq)
        p, q = Implication.extract(pq_conc)
        return self.imp_transitivity(pq, lambda: self.dynamic_inst(self.prop1, {0: q, 1: r}))

    # (p -> q) -> (~q -> ~p)
    def con3(self, p: Pattern, q: Pattern) -> Proved:
        return self.imp_trans(p, q, bot)

    # p -> q
    # ----------
    # ~q -> ~p
    def con3_i(self, pq: ProvedExpression) -> Proved:
        pq_conc = self.PROVISIONAL_get_conc(pq)
        p, q = Implication.extract(pq_conc)
        return self.modus_ponens(self.con3(p, q), pq())

    #      p -> q
    # ----------------
    #   ~q -> p -> r
    def absurd2(self, pq: ProvedExpression, r: Pattern) -> Proved:
        pq_conc = self.PROVISIONAL_get_conc(pq)
        p, q = Implication.extract(pq_conc)
        return self.imp_transitivity(
            lambda: self.absurd(q, r),
            lambda: self.modus_ponens(self.imp_trans(p, q, r), pq())
        )

    #   ~p -> q     ~r
    # ------------------
    #   (q -> r) -> p
    def absurd3(self, npq: ProvedExpression, nr: ProvedExpression) -> Proved:
        npq_conc = self.PROVISIONAL_get_conc(npq)
        nr_conc = self.PROVISIONAL_get_conc(nr)
        np, q = Implication.extract(npq_conc)
        p = Negation.extract(np)
        r = Negation.extract(nr_conc)
        # TODO
        return Proved(self.interpreter, Implication(Implication(q, r), p))

    #   p -> ~q
    # ------------------
    #   q -> p -> r
    def absurd4(self, pnq_pf: ProvedExpression, r: Pattern) -> Proved:
        pnq = self.PROVISIONAL_get_conc(pnq_pf)
        p, nq = Implication.extract(pnq)
        q = Negation.extract(nq)
        return self.imp_transitivity(lambda: self.dni(q), lambda: self.absurd2(pnq, r))

    #   ~p
    # -----------
    #  p -> q
    def absurd_i(self, np_pf: ProvedExpression, q: Pattern) -> Proved:
        np = self.PROVISIONAL_get_conc(np_pf)
        p = Negation.extract(np)
        return self.modus_ponens(self.absurd(p, q), np())

    #   p   ~q
    # -----------
    #  ~(p -> q)
    def and_not_r_intro(self, p_pf: ProvedExpression, nq_pf: ProvedExpression) -> Proved:
        p = self.PROVISIONAL_get_conc(p_pf)
        nq = self.PROVISIONAL_get_conc(nq_pf)
        q = Negation.extract(nq)
        # TODO
        return Proved(self.interpreter, neg(Implication(p, q)))

    # (a -> b)    (c -> d)
    # ---------------------
    # (b -> c) -> (a -> d)
    def imim(self, h1: ProvedExpression, h2: ProvedExpression) -> Proved:
        h1_conc = self.PROVISIONAL_get_conc(h1)
        h2_conc = self.PROVISIONAL_get_conc(h2)
        a, b = Implication.extract(h1_conc)
        c, d = Implication.extract(h2_conc)
        # TODO
        return Proved(self.interpreter, Implication(Implication(b, c), Implication(a, d)))

    # (a -> b)    (c -> d)
    # ---------------------
    # (b -> c) -> (~~a -> d)
    def imim_nnr(self, h1: ProvedExpression, h2: ProvedExpression) -> Proved:
        h1_conc = self.PROVISIONAL_get_conc(h1)
        h2_conc = self.PROVISIONAL_get_conc(h2)
        a, b = Implication.extract(h1_conc)
        c, d = Implication.extract(h2_conc)
        return self.imp_transitivity(
            lambda: self.imim(h1, h2),
            lambda: self.modus_ponens(self.imp_trans(neg(neg(a)), a, d), self.dynamic_inst(self.prop3, {0: a})),
        )

    # (a -> b)    (c -> d)
    # ---------------------
    # (~~b -> c) -> (a -> d)
    def imim_nnl(self, h1: ProvedExpression, h2: ProvedExpression) -> Proved:
        h1_conc = self.PROVISIONAL_get_conc(h1)
        h2_conc = self.PROVISIONAL_get_conc(h2)
        a, b = Implication.extract(h1_conc)
        c, d = Implication.extract(h2_conc)
        return self.imp_transitivity(
            lambda: self.modus_ponens(self.imp_trans(b, neg(neg(b)), c), self.dni(b)),
            lambda: self.imim(h1, h2)
        )

    # (a -> b)   (c -> d)
    # ---------------------
    # a \/ c -> b \/ d
    def imim_or(self, h1: ProvedExpression, h2: ProvedExpression) -> Proved:
        return self.imim(lambda: self.con3_i(h1), h2)

    # (a -> b)   (c -> d)
    # ---------------------
    # a /\ c -> b /\ d
    def imim_and(self, h1: ProvedExpression, h2: ProvedExpression) -> Proved:
        return self.con3_i(lambda: self.imim(h1, lambda: self.con3_i(h2)))

    # (b -> c)
    # ---------------------
    # a /\ b -> a /\ c
    def imim_and_r(self, pat: Pattern, h: ProvedExpression) -> Proved:
        h_conc = self.PROVISIONAL_get_conc(h)
        b, c = Implication.extract(h_conc)
        # TODO
        return Proved(self.interpreter, Implication(And(pat, b), And(pat, c)))

    # (a -> b)
    # ---------------------
    # a /\ c -> b /\ c
    def imim_and_l(self, pat: Pattern, h: ProvedExpression) -> Proved:
        h_conc = self.PROVISIONAL_get_conc(h)
        a, b = Implication.extract(h_conc)
        # TODO
        return Proved(self.interpreter, Implication(And(a, pat), And(b, pat)))

    # (b -> c)
    # ---------------------
    # a \/ b -> a \/ c
    def imim_or_r(self, pat: Pattern, h: ProvedExpression) -> Proved:
        h_conc = self.PROVISIONAL_get_conc(h)
        b, c = Implication.extract(h_conc)
        # TODO
        return Proved(self.interpreter, Implication(Or(pat, b), Or(pat, c)))

    # (a -> b)
    # ---------------------
    # a \/ c -> b \/ c
    def imim_or_l(self, pat: Pattern, h: ProvedExpression) -> Proved:
        h_conc = self.PROVISIONAL_get_conc(h)
        a, b = Implication.extract(h_conc)
        # TODO
        return Proved(self.interpreter, Implication(Or(a, pat), Or(b, pat)))

    # (a /\ b) /\ c -> a /\ (b /\ c)
    def and_assoc_r(self, pat1: Pattern = phi0, pat2: Pattern = phi1, pat3: Pattern = phi2) -> Proved:
        # TODO
        return Proved(self.interpreter, Implication(And(And(pat1, pat2), pat3), And(pat1, And(pat2, pat3))))

    # a /\ (b /\ c) -> (a /\ b) /\ c
    def and_assoc_l(self, pat1: Pattern = phi0, pat2: Pattern = phi1, pat3: Pattern = phi2) -> Proved:
        # TODO
        return Proved(self.interpreter, Implication(And(pat1, And(pat2, pat3)), And(And(pat1, pat2), pat3)))

    # (a \/ b) \/ c -> a \/ (b \/ c)
    def or_assoc_r(self, pat1: Pattern = phi0, pat2: Pattern = phi1, pat3: Pattern = phi2) -> Proved:
        # TODO
        return Proved(self.interpreter, Implication(Or(Or(pat1, pat2), pat3), Or(pat1, Or(pat2, pat3))))

    # a \/ (b \/ c) -> (a \/ b) \/ c
    def or_assoc_l(self, pat1: Pattern = phi0, pat2: Pattern = phi1, pat3: Pattern = phi2) -> Proved:
        # TODO
        return Proved(self.interpreter, Implication(Or(pat1, Or(pat2, pat3)), Or(Or(pat1, pat2), pat3)))

    # (a /\ b) \/ c -> (a \/ c) /\ (b \/ c)
    def or_distr_r(self, pat1: Pattern = phi0, pat2: Pattern = phi1, pat3: Pattern = phi2) -> Proved:
        # TODO
        return Proved(
            self.interpreter, Implication(Or(And(pat1, pat2), pat3), And(Or(pat1, pat3), Or(pat2, pat3)))
        )

    # (a \/ c) /\ (b \/ c) -> (a /\ b) \/ c
    def or_distr_r_rev(
        self, pat1: Pattern = phi0, pat2: Pattern = phi1, pat3: Pattern = phi2
    ) -> Proved:
        # TODO
        return Proved(
            self.interpreter, Implication(And(Or(pat1, pat3), Or(pat2, pat3)), Or(And(pat1, pat2), pat3))
        )

    # a \/ (b /\ c) -> (a \/ b) /\ (a \/ c)
    def or_distr_l(self, pat1: Pattern = phi0, pat2: Pattern = phi1, pat3: Pattern = phi2) -> Proved:
        # TODO
        return Proved(
            self.interpreter, Implication(Or(pat1, And(pat2, pat3)), And(Or(pat1, pat2), Or(pat1, pat3)))
        )

    # (a \/ b) /\ (a \/ c) -> a \/ (b /\ c)
    def or_distr_l_rev(
        self, pat1: Pattern = phi0, pat2: Pattern = phi1, pat3: Pattern = phi2
    ) -> Proved:
        # TODO
        return Proved(
            self.interpreter, Implication(And(Or(pat1, pat2), Or(pat1, pat3)), Or(pat1, And(pat2, pat3)))
        )

    def is_propositional(self, pat: Pattern) -> bool:
        if Bot.is_bot(pat):
            return True
        if pat_imp := Implication.unwrap(pat):
            return self.is_propositional(pat_imp[0]) and self.is_propositional(pat_imp[1])
        if isinstance(pat, MetaVar):
            return True
        if isinstance(pat, Notation):
            return self.is_propositional(pat.conclusion())
        return False

    def conj_to_pattern(self, term: ConjTerm) -> Pattern:
        if isinstance(term, ConjBool):
            pat = bot
        elif isinstance(term, ConjVar):
            pat = MetaVar(term.id)
        elif isinstance(term, ConjOr):
            pat = Or(self.conj_to_pattern(term.left), self.conj_to_pattern(term.right))
        elif isinstance(term, ConjAnd):
            pat = And(self.conj_to_pattern(term.left), self.conj_to_pattern(term.right))
        if term.negated:
            pat = neg(pat)
        return pat

    # Assumes the input is a propositional formula and transforms it to one
    # made up of only ORs, negations and variables
    # Output is:
    #   the representation of the new term
    #   proof that old term -> new term
    #   proof that new term -> old term
    # NOTE! When the new term is Top or Bottom, we only populate the
    # first proof; this proof will be a proof of `old term` or `neg(old term)`
    # respectively (as opposed to, say, `old term -> Top``)
    def to_conj(self, pat: Pattern) -> tuple[ConjTerm, ProvedExpression, ProvedExpression | None]:
        if Bot.is_bot(pat):
            return ConjBool(False), self.top_intro, None
        if Top.is_top(pat):
            return ConjBool(True), self.top_intro, None
        match pat:
            case MetaVar(id):
                phi_imp_phi = self.imp_refl(pat)
                return ConjVar(id), phi_imp_phi, phi_imp_phi
            case Implication(phi0, phi1):
                phi1_conj, phi1_l, phi1_r = self.to_conj(phi1)

                if isinstance(phi1_conj, ConjBool):
                    if phi1_conj.negated:
                        pf = self.imp_provable(phi0, phi1_l)
                        return ConjBool(True), pf, None
                    else:
                        # TODO Consider whether it's worth adding a special branch here
                        # to optimize for early construction of AND terms:
                        # if isinstance(phi0, Implication):
                        #     ...
                        phi0_conj, phi0_l, phi0_r = self.to_conj(phi0)
                        if isinstance(phi0_conj, ConjBool):
                            if phi0_conj.negated:
                                pf = self.and_not_r_intro(phi0_l, phi1_l)
                                return ConjBool(False), pf, None
                            else:
                                pf = self.absurd_i(phi0_l, phi1)
                                return ConjBool(True), pf, None
                        if phi0_conj.negated:
                            phi0_conj.negated = False
                            return phi0_conj, self.absurd3(phi0_r, phi1_l), self.absurd4(phi0_l, phi1)
                        else:
                            phi0_conj.negated = True
                            return phi0_conj, self.imim(phi0_r, phi1_l), self.absurd2(phi0_l, phi1)
                phi0_conj, phi0_l, phi0_r = self.to_conj(phi0)
                if isinstance(phi0_conj, ConjBool):
                    if phi0_conj.negated:
                        return phi1_conj, self.helper1(phi0_l, phi1_l), self.a1d(phi1_r, phi0)
                    else:
                        pf = self.absurd_i(phi0_l, phi1)
                        return ConjBool(True), pf, None
                if phi0_conj.negated:
                    phi0_conj.negated = False
                    return ConjOr(phi0_conj, phi1_conj), self.imim(phi0_r, phi1_l), self.imim(phi0_l, phi1_r)
                else:
                    phi0_conj.negated = True
                    return ConjOr(phi0_conj, phi1_conj), self.imim_nnr(phi0_r, phi1_l), self.imim_nnl(phi0_l, phi1_r)
            case _:
                # TODO Add more context to this error message
                raise AssertionError('Unexpected pattern')

    # Assumes `term` is made up only of OR nodes and vars (+ single negations)
    def propag_neg(self, term: ConjTerm) -> Tuple[ConjTerm, Proved, Proved]:
        if isinstance(term, ConjVar):
            phi_imp_phi = self.imp_refl(MetaVar(term.id))
            return term, phi_imp_phi, phi_imp_phi
        elif isinstance(term, ConjOr):
            if term.negated:
                term.left.negated = not term.left.negated
                term.right.negated = not term.right.negated
                term_l, term_l_pf1, term_l_pf2 = self.propag_neg(term.left)
                term_r, term_r_pf1, term_r_pf2 = self.propag_neg(term.right)
                if not term.left.negated:
                    term_l_pf1 = self.dni_l_i(term_l_pf1)
                    term_l_pf2 = self.dni_r_i(term_l_pf2)
                pf1 = self.imim_and(term_l_pf1, term_r_pf1)
                pf2 = self.imim_and(term_l_pf2, term_r_pf2)
                if term.right.negated:
                    a1, b1 = self.get_imp(self.get_neg(pf1.conclusion.left))
                    pf1 = self.imp_trans_i(self.con3_i(self.dne_r(a1, b1)), pf1)
                    a2, nnb2 = self.get_imp(self.get_neg(pf2.conclusion.right))
                    b2 = self.get_neg(self.get_neg(nnb2))
                    pf2 = self.imp_trans_i(pf2, self.con3_i(self.dni_r(a2, b2)))
                return ConjAnd(term_l, term_r), pf1, pf2
            else:
                term_l, term_l_pf1, term_l_pf2 = self.propag_neg(term.left)
                term_r, term_r_pf1, term_r_pf2 = self.propag_neg(term.right)
                return (
                    ConjOr(term_l, term_r),
                    self.imim_or(term_l_pf1, term_r_pf1),
                    self.imim_or(term_l_pf2, term_r_pf2),
                )
        else:
            # TODO Add more context to this error message
            raise AssertionError('Unexpected pattern')

    # Assumes negation has been fully propagated through the term
    def to_cnf(self, term: ConjTerm) -> Tuple[ConjTerm, Proved, Proved]:
        if isinstance(term, ConjVar):
            phi_imp_phi = self.imp_refl(MetaVar(term.id))
            return term, phi_imp_phi, phi_imp_phi
        elif isinstance(term, ConjAnd):
            term_l, term_l_pf1, term_l_pf2 = self.to_cnf(term.left)
            term_r, term_r_pf1, term_r_pf2 = self.to_cnf(term.right)
            pf1 = self.imim_and(term_l_pf1, term_r_pf1)
            pf2 = self.imim_and(term_l_pf2, term_r_pf2)
            return ConjAnd(term_l, term_r), pf1, pf2
        elif isinstance(term, ConjOr):
            term_l, term_l_pf1, term_l_pf2 = self.to_cnf(term.left)
            term_r, term_r_pf1, term_r_pf2 = self.to_cnf(term.right)
            pf1 = self.imim_or(term_l_pf1, term_r_pf1)
            pf2 = self.imim_or(term_l_pf2, term_r_pf2)
            pf1_conc = pf1.conclusion
            assert isinstance(pf1_conc, Implication)
            if isinstance(term_l, ConjAnd):
                pf1 = self.imp_trans_match2(pf1, self.or_distr_r())
                pf2 = self.imp_trans_match1(self.or_distr_r_rev(), pf2)
                new_term, pf1_, pf2_ = self.to_cnf(ConjAnd(ConjOr(term_l.left, term_r), ConjOr(term_l.right, term_r)))
                pf1 = self.imp_trans_i(pf1, pf1_)
                pf2 = self.imp_trans_i(pf2_, pf2)
                return new_term, pf1, pf2
            elif isinstance(term_r, ConjAnd):
                pf1 = self.imp_trans_match2(pf1, self.or_distr_l())
                pf2 = self.imp_trans_match1(self.or_distr_l_rev(), pf2)
                new_term, pf1_, pf2_ = self.to_cnf(ConjAnd(ConjOr(term_l, term_r.left), ConjOr(term_l, term_r.right)))
                pf1 = self.imp_trans_i(pf1, pf1_)
                pf2 = self.imp_trans_i(pf2_, pf2)
                return new_term, pf1, pf2
            else:
                return ConjOr(term_l, term_r), pf1, pf2
        else:
            # TODO Add more context to this error message
            raise AssertionError('Unexpected pattern')

    # Assumes term is in CNF form
    def to_clauses(self, term: ConjTerm) -> Tuple[List[List[int]], Proved, Proved]:
        if isinstance(term, ConjVar):
            if term.negated:
                id = -term.id
            else:
                id = term.id
            phi_imp_phi = self.imp_refl(MetaVar(term.id))
            return [[id]], phi_imp_phi, phi_imp_phi
        elif isinstance(term, ConjAnd):
            term_l, term_l_pf1, term_l_pf2 = self.to_clauses(term.left)
            term_r, term_r_pf1, term_r_pf2 = self.to_clauses(term.right)
            pf1 = self.imim_and(term_l_pf1, term_r_pf1)
            pf2 = self.imim_and(term_l_pf2, term_r_pf2)
            l = len(term_l)
            assert l > 0
            if l > 1:
                shift_right = self.and_assoc_r()
                shift_left = self.and_assoc_l()
                for i in range(0, l - 2):
                    shift_right = self.imp_trans_match1(
                        self.and_assoc_r(), self.imim_and_r(MetaVar(i + 3), shift_right)
                    )
                    shift_left = self.imp_trans_match2(self.imim_and_r(MetaVar(i + 3), shift_left), self.and_assoc_l())
                pf1 = self.imp_trans_match2(pf1, shift_right)
                pf2 = self.imp_trans_match1(shift_left, pf2)
            return term_l + term_r, pf1, pf2
        elif isinstance(term, ConjOr):
            term_l, term_l_pf1, term_l_pf2 = self.to_clauses(term.left)
            term_r, term_r_pf1, term_r_pf2 = self.to_clauses(term.right)
            pf1 = self.imim_or(term_l_pf1, term_r_pf1)
            pf2 = self.imim_or(term_l_pf2, term_r_pf2)
            assert len(term_l) == 1
            assert len(term_r) == 1
            l = len(term_l[0])
            assert l > 0
            if l > 1:
                shift_right = self.or_assoc_r()
                shift_left = self.or_assoc_l()
                for i in range(0, l - 2):
                    shift_right = self.imp_trans_match1(self.or_assoc_r(), self.imim_or_r(MetaVar(i + 3), shift_right))
                    shift_left = self.imp_trans_match2(self.imim_or_r(MetaVar(i + 3), shift_left), self.or_assoc_l())
                pf1 = self.imp_trans_match2(pf1, shift_right)
                pf2 = self.imp_trans_match1(shift_left, pf2)
            return [term_l[0] + term_r[0]], pf1, pf2
