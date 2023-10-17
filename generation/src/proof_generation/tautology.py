from __future__ import annotations

from functools import partial
from typing import TYPE_CHECKING, List

from proof_generation.matching import match_single
from proof_generation.pattern import Bot, Implication, MetaVar, Notation
from proof_generation.proofs.propositional import And, Negation, Or, Propositional, Top, bot, neg, phi0, phi1, phi2
from proof_generation.proved import Proved

if TYPE_CHECKING:
    from proof_generation.pattern import Pattern
    from proof_generation.proof import ProvedExpression


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


class Tautology(Propositional):
    def imp_trans_match1(self, h1: ProvedExpression, h2: ProvedExpression) -> Proved:
        """ """
        h1_conc = self.PROVISIONAL_get_conc(h1)
        h2_conc = self.PROVISIONAL_get_conc(h2)
        _, b = Implication.extract(h1_conc)
        c, _ = Implication.extract(h2_conc)
        subst = match_single(b, c, {})
        assert subst is not None
        actual_subst: dict[int, Pattern] = subst
        return self.imp_transitivity(lambda: self.dynamic_inst(h1, actual_subst), h2)

    def imp_trans_match2(self, h1: ProvedExpression, h2: ProvedExpression) -> Proved:
        """ """
        h1_conc = self.PROVISIONAL_get_conc(h1)
        h2_conc = self.PROVISIONAL_get_conc(h2)
        _, b = Implication.extract(h1_conc)
        c, _ = Implication.extract(h2_conc)
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
        pq = Implication(p, q)
        return self.modus_ponens(
            self.modus_ponens(self.dynamic_inst(self.prop2, {0: pq, 1: p, 2: q}), self.imp_refl(pq)),
            self.imp_provable(pq, p_pf),
        )

    def imp_trans(self, p: Pattern, q: Pattern, r: Pattern) -> Proved:
        """(p -> q) -> (q -> r) -> p -> r"""
        # TODO
        return Proved(Implication(Implication(p, q), Implication(Implication(q, r), Implication(p, r))))

    def dni(self, p: Pattern) -> Proved:
        """p -> ~~p"""
        # TODO
        return Proved(Implication(p, neg(neg(p))))

    def dni_l(self, p: Pattern, q: Pattern) -> Proved:
        """ """
        return self.modus_ponens(self.imp_trans(neg(neg(p)), p, q), self.dynamic_inst(self.prop3, {0: p}))

    def dni_l_i(self, pq: ProvedExpression) -> Proved:
        """ """
        pq_conc = self.PROVISIONAL_get_conc(pq)
        p, q = Implication.extract(pq_conc)
        return self.modus_ponens(self.dni_l(p, q), pq())

    def dni_r(self, p: Pattern, q: Pattern) -> Proved:
        """ """
        return self.modus_ponens(
            self.dynamic_inst(self.prop2, {0: p, 1: q, 2: neg(neg(q))}), self.imp_provable(p, lambda: self.dni(q))
        )

    def dni_r_i(self, pq: ProvedExpression) -> Proved:
        """ """
        pq_conc = self.PROVISIONAL_get_conc(pq)
        p, q = Implication.extract(pq_conc)
        return self.modus_ponens(self.dni_r(p, q), pq())

    def dne_l(self, p: Pattern, q: Pattern) -> Proved:
        """ """
        return self.modus_ponens(self.imp_trans(p, neg(neg(p)), q), self.dni(p))

    def dne_l_i(self, pq: ProvedExpression) -> Proved:
        """ """
        pq_conc = self.PROVISIONAL_get_conc(pq)
        p, q = Implication.extract(pq_conc)
        return self.modus_ponens(self.dne_l(p, q), pq())

    def dne_r(self, p: Pattern, q: Pattern) -> Proved:
        """ """
        return self.modus_ponens(
            self.dynamic_inst(self.prop2, {0: p, 1: neg(neg(q)), 2: q}),
            self.imp_provable(p, lambda: self.dynamic_inst(self.prop3, {0: q})),
        )

    def dne_r_i(self, pq: ProvedExpression) -> Proved:
        """ """
        pq_conc = self.PROVISIONAL_get_conc(pq)
        p, q = Implication.extract(pq_conc)
        return self.modus_ponens(self.dne_r(p, q), pq())

    def helper1(self, p_pf: ProvedExpression, qr_pf: ProvedExpression) -> Proved:
        """
           p    q -> r
        -----------------
          (p -> q) -> r
        """
        qr = self.PROVISIONAL_get_conc(qr_pf)
        q, r = Implication.extract(qr)
        return self.imp_transitivity(lambda: self.mpcom(p_pf, q), qr_pf)

    def a1d(self, pq: ProvedExpression, r: Pattern) -> Proved:
        """
             p -> q
        ---------------
          p -> r -> q
        """
        pq_conc = self.PROVISIONAL_get_conc(pq)
        p, q = Implication.extract(pq_conc)
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
        p, q = Implication.extract(pq_conc)
        return self.modus_ponens(self.con3(p, q), pq())

    def absurd2(self, pq: ProvedExpression, r: Pattern) -> Proved:
        """
             p -> q
        -----------------
           ~q -> p -> r
        """
        pq_conc = self.PROVISIONAL_get_conc(pq)
        p, q = Implication.extract(pq_conc)
        return self.imp_transitivity(
            lambda: self.absurd(q, r), lambda: self.modus_ponens(self.imp_trans(p, q, r), pq())
        )

    def absurd3(self, npq: ProvedExpression, nr: ProvedExpression) -> Proved:
        """
           ~p -> q     ~r
        -------------------
           (q -> r) -> p
        """
        npq_conc = self.PROVISIONAL_get_conc(npq)
        nr_conc = self.PROVISIONAL_get_conc(nr)
        np, q = Implication.extract(npq_conc)
        p = Negation.extract(np)
        r = Negation.extract(nr_conc)
        # TODO
        return Proved(Implication(Implication(q, r), p))

    def absurd4(self, pnq_pf: ProvedExpression, r: Pattern) -> Proved:
        """
           p -> ~q
        ------------------
           q -> p -> r
        """
        pnq = self.PROVISIONAL_get_conc(pnq_pf)
        p, nq = Implication.extract(pnq)
        q = Negation.extract(nq)
        return self.imp_transitivity(lambda: self.dni(q), lambda: self.absurd2(pnq_pf, r))

    def absurd_i(self, np_pf: ProvedExpression, q: Pattern) -> Proved:
        """
           ~p
        -----------
          p -> q
        """
        np = self.PROVISIONAL_get_conc(np_pf)
        p = Negation.extract(np)
        return self.modus_ponens(self.absurd(p, q), np_pf())

    def and_not_r_intro(self, p_pf: ProvedExpression, nq_pf: ProvedExpression) -> Proved:
        """
           p   ~q
        -------------
          ~(p -> q)
        """
        p = self.PROVISIONAL_get_conc(p_pf)
        nq = self.PROVISIONAL_get_conc(nq_pf)
        q = Negation.extract(nq)
        # TODO
        return Proved(neg(Implication(p, q)))

    def imim(self, h1: ProvedExpression, h2: ProvedExpression) -> Proved:
        """
        (a -> b)    (c -> d)
        ---------------------
        (b -> c) -> (a -> d)
        """
        h1_conc = self.PROVISIONAL_get_conc(h1)
        h2_conc = self.PROVISIONAL_get_conc(h2)
        a, b = Implication.extract(h1_conc)
        c, d = Implication.extract(h2_conc)
        # TODO
        return Proved(Implication(Implication(b, c), Implication(a, d)))

    def imim_nnr(self, h1: ProvedExpression, h2: ProvedExpression) -> Proved:
        """
        (a -> b)    (c -> d)
        ---------------------
        (b -> c) -> (~~a -> d)
        """
        h1_conc = self.PROVISIONAL_get_conc(h1)
        h2_conc = self.PROVISIONAL_get_conc(h2)
        a, b = Implication.extract(h1_conc)
        c, d = Implication.extract(h2_conc)
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
        a, b = Implication.extract(h1_conc)
        c, d = Implication.extract(h2_conc)
        return self.imp_transitivity(
            lambda: self.modus_ponens(self.imp_trans(b, neg(neg(b)), c), self.dni(b)), lambda: self.imim(h1, h2)
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
        h_conc = self.PROVISIONAL_get_conc(h)
        b, c = Implication.extract(h_conc)
        # TODO
        return Proved(Implication(And(pat, b), And(pat, c)))

    def imim_and_l(self, pat: Pattern, h: ProvedExpression) -> Proved:
        """
            (a -> b)
        ---------------------
           a /\\ c -> b /\\ c
        """
        h_conc = self.PROVISIONAL_get_conc(h)
        a, b = Implication.extract(h_conc)
        # TODO
        return Proved(Implication(And(a, pat), And(b, pat)))

    def imim_or_r(self, pat: Pattern, h: ProvedExpression) -> Proved:
        """
             (b -> c)
        ---------------------
            a \\/ b -> a \\/ c
        """
        h_conc = self.PROVISIONAL_get_conc(h)
        b, c = Implication.extract(h_conc)
        # TODO
        return Proved(Implication(Or(pat, b), Or(pat, c)))

    def imim_or_l(self, pat: Pattern, h: ProvedExpression) -> Proved:
        """
              (a -> b)
        ---------------------
           a \\/ c -> b \\/ c
        """
        h_conc = self.PROVISIONAL_get_conc(h)
        a, b = Implication.extract(h_conc)
        # TODO
        return Proved(Implication(Or(a, pat), Or(b, pat)))

    def and_assoc_r(self, pat1: Pattern = phi0, pat2: Pattern = phi1, pat3: Pattern = phi2) -> Proved:
        """(a /\\ b) /\\ c -> a /\\ (b /\\ c)"""
        # TODO
        return Proved(Implication(And(And(pat1, pat2), pat3), And(pat1, And(pat2, pat3))))

    def and_assoc_l(self, pat1: Pattern = phi0, pat2: Pattern = phi1, pat3: Pattern = phi2) -> Proved:
        """a /\\ (b /\\ c) -> (a /\\ b) /\\ c"""
        # TODO
        return Proved(Implication(And(pat1, And(pat2, pat3)), And(And(pat1, pat2), pat3)))

    def or_assoc_r(self, pat1: Pattern = phi0, pat2: Pattern = phi1, pat3: Pattern = phi2) -> Proved:
        """(a \\/ b) \\/ c -> a \\/ (b \\/ c)"""
        # TODO
        return Proved(Implication(Or(Or(pat1, pat2), pat3), Or(pat1, Or(pat2, pat3))))

    def or_assoc_l(self, pat1: Pattern = phi0, pat2: Pattern = phi1, pat3: Pattern = phi2) -> Proved:
        """a \\/ (b \\/ c) -> (a \\/ b) \\/ c"""
        # TODO
        return Proved(Implication(Or(pat1, Or(pat2, pat3)), Or(Or(pat1, pat2), pat3)))

    def or_distr_r(self, pat1: Pattern = phi0, pat2: Pattern = phi1, pat3: Pattern = phi2) -> Proved:
        """(a /\\ b) \\/ c -> (a \\/ c) /\\ (b \\/ c)"""
        # TODO
        return Proved(Implication(Or(And(pat1, pat2), pat3), And(Or(pat1, pat3), Or(pat2, pat3))))

    def or_distr_r_rev(self, pat1: Pattern = phi0, pat2: Pattern = phi1, pat3: Pattern = phi2) -> Proved:
        """(a \\/ c) /\\ (b \\/ c) -> (a /\\ b) \\/ c"""
        # TODO
        return Proved(Implication(And(Or(pat1, pat3), Or(pat2, pat3)), Or(And(pat1, pat2), pat3)))

    def or_distr_l(self, pat1: Pattern = phi0, pat2: Pattern = phi1, pat3: Pattern = phi2) -> Proved:
        """a \\/ (b /\\ c) -> (a \\/ b) /\\ (a \\/ c)"""
        # TODO
        return Proved(Implication(Or(pat1, And(pat2, pat3)), And(Or(pat1, pat2), Or(pat1, pat3))))

    def or_distr_l_rev(self, pat1: Pattern = phi0, pat2: Pattern = phi1, pat3: Pattern = phi2) -> Proved:
        """(a \\/ b) /\\ (a \\/ c) -> a \\/ (b /\\ c)"""
        # TODO
        return Proved(Implication(And(Or(pat1, pat2), Or(pat1, pat3)), Or(pat1, And(pat2, pat3))))

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
        if Bot.is_bot(pat):
            return ConjBool(False), self.top_intro, None
        if Top.is_top(pat):
            return ConjBool(True), self.top_intro, None
        if isinstance(pat, MetaVar):
            phi_imp_phi = lambda: self.imp_refl(pat)
            return ConjVar(pat.name), phi_imp_phi, phi_imp_phi
        elif pat_imp := Implication.extract(pat):
            pat0 = pat_imp[0]
            pat1 = pat_imp[1]
            pat1_conj, pat1_l, pat1_r = self.to_conj(pat1)

            if isinstance(pat1_conj, ConjBool):
                if pat1_conj.negated:
                    pf = lambda: self.imp_provable(pat0, pat1_l)
                    return ConjBool(True), pf, None
                else:
                    # TODO Consider whether it's worth adding a special branch here
                    # to optimize for early construction of AND terms:
                    # if isinstance(pat0, Implication):
                    #     ...
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
            phi_imp_phi = lambda: self.imp_refl(MetaVar(term.id))
            return term, phi_imp_phi, phi_imp_phi
        elif isinstance(term, ConjOr):
            if term.negated:
                term.left.negated = not term.left.negated
                term.right.negated = not term.right.negated
                term_l, term_l_pf1, term_l_pf2 = self.propag_neg(term.left)
                term_r, term_r_pf1, term_r_pf2 = self.propag_neg(term.right)
                if not term.left.negated:
                    term_l_pf1 = lambda: self.dni_l_i(term_l_pf1)
                    term_l_pf2 = lambda: self.dni_r_i(term_l_pf2)
                pf1 = lambda: self.imim_and(term_l_pf1, term_r_pf1)
                pf2 = lambda: self.imim_and(term_l_pf2, term_r_pf2)
                if term.right.negated:
                    pf1_conc = self.PROVISIONAL_get_conc(pf1)
                    pf1_l, pf1_r = Implication.extract(pf1_conc)
                    a1, b1 = Implication.extract(Negation.extract(pf1_l))
                    pf1 = lambda: self.imp_transitivity(lambda: self.con3_i(lambda: self.dne_r(a1, b1)), pf1)
                    pf2_conc = self.PROVISIONAL_get_conc(pf2)
                    pf2_l, pf2_r = Implication.extract(pf2_conc)
                    a2, nnb2 = Implication.extract(Negation.extract(pf2_r))
                    b2 = Negation.extract(Negation.extract(nnb2))
                    pf2 = lambda: self.imp_transitivity(pf2, lambda: self.con3_i(lambda: self.dni_r(a2, b2)))
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
            phi_imp_phi = lambda: self.imp_refl(MetaVar(term.id))
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
            Implication.extract(pf1_conc)
            if isinstance(term_l, ConjAnd):
                pf1 = lambda: self.imp_trans_match2(pf1, self.or_distr_r)
                pf2 = lambda: self.imp_trans_match1(self.or_distr_r_rev, pf2)
                new_term, pf1_, pf2_ = self.to_cnf(ConjAnd(ConjOr(term_l.left, term_r), ConjOr(term_l.right, term_r)))
                pf1 = lambda: self.imp_transitivity(pf1, pf1_)
                pf2 = lambda: self.imp_transitivity(pf2_, pf2)
                return new_term, pf1, pf2
            elif isinstance(term_r, ConjAnd):
                pf1 = lambda: self.imp_trans_match2(pf1, self.or_distr_l)
                pf2 = lambda: self.imp_trans_match1(self.or_distr_l_rev, pf2)
                new_term, pf1_, pf2_ = self.to_cnf(ConjAnd(ConjOr(term_l, term_r.left), ConjOr(term_l, term_r.right)))
                pf1 = lambda: self.imp_transitivity(pf1, pf1_)
                pf2 = lambda: self.imp_transitivity(pf2_, pf2)
                return new_term, pf1, pf2
            else:
                return ConjOr(term_l, term_r), pf1, pf2
        else:
            raise AssertionError(f'Unexpected pattern! Expected a term with only Or and And but got:\n{str(term)}\n')

    def to_clauses(self, term: ConjTerm) -> tuple[list[list[int]], ProvedExpression, ProvedExpression]:
        """Assumes term is in CNF form"""
        if isinstance(term, ConjVar):
            if term.negated:
                id = -term.id
            else:
                id = term.id
            phi_imp_phi = lambda: self.imp_refl(MetaVar(term.id))
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
                            partial(
                                lambda i, shift_right: self.imim_and_r(MetaVar(i + 3), shift_right), i, shift_right
                            ),
                        ),
                        i,
                        shift_right,
                    )
                    shift_left = partial(
                        lambda i, shift_left: self.imp_trans_match2(
                            partial(lambda i, shift_left: self.imim_and_r(MetaVar(i + 3), shift_left), i, shift_left),
                            self.and_assoc_l,
                        ),
                        i,
                        shift_left,
                    )
                pf1 = lambda: self.imp_trans_match2(pf1, shift_right)
                pf2 = lambda: self.imp_trans_match1(shift_left, pf2)
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
                            partial(lambda i, shift_right: self.imim_or_r(MetaVar(i + 3), shift_right), i, shift_right),
                        ),
                        i,
                        shift_right,
                    )
                    shift_left = partial(
                        lambda i, shift_left: self.imp_trans_match2(
                            partial(lambda i, shift_left: self.imim_or_r(MetaVar(i + 3), shift_left), i, shift_left),
                            self.or_assoc_l,
                        ),
                        i,
                        shift_left,
                    )
                pf1 = lambda: self.imp_trans_match2(pf1, shift_right)
                pf2 = lambda: self.imp_trans_match1(shift_left, pf2)
            return [term_l[0] + term_r[0]], pf1, pf2
        else:
            raise AssertionError(
                f'Unexpected pattern! Expected a term with only Or, And and Negations but got:\n{str(term)}\n'
            )
