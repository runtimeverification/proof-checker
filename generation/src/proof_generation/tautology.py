from __future__ import annotations
from ast import Tuple

import sys
from typing import TYPE_CHECKING

from proof_generation.proof import Implication, MetaVar, Mu, ProofExp, SVar

if TYPE_CHECKING:
    from proof_generation.proof import BasicInterpreter, Pattern, PatternExpression, Proved, ProvedExpression
    from proof_generation.proofs.propositional import Propositional

#TODO These should be defined somewhere so that all importing files use the same definition
bot = Mu(SVar(0), SVar(0))
def neg(pat: Pattern) -> Pattern:
    return Implication(pat, bot)
top = neg(bot)

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

    def is_neg(self, pat: Pattern) -> bool:
        if isinstance(pat, Implication):
            return pat.right == bot
        return False

    def get_imp(self, pat: Pattern) -> Tuple[Pattern, Pattern]:
        assert isinstance(pat, Implication)
        return pat.left, pat.right

    def get_neg(self, pat: Pattern) -> Pattern:
        assert isinstance(pat, Implication)
        assert pat.right == bot
        return pat.left

    # p -> p
    def imp_refl(self, p: Pattern) -> Proved:
        return self.dynamic_inst(self.imp_reflexivity, {0: p})

    #        p
    # -----------------
    #   (p -> q) -> q
    def mpcom(self, p_pf: Proved, q: Pattern) -> Proved:
        p = p_pf.conclusion
        pq = Implication(p, q)
        pf = self.modus_ponens(
            self.dynamic_inst(self.prop2, {0: pq, 1: p, 2: q}),
            self.imp_refl(pq))
        return self.modus_ponens(pf, self.imp_provable(pq, p_pf))

    # p -> ~~p
    def dni(self, p: Pattern) -> Proved:
        ...

    def dni_l(self, p: Pattern, q: Pattern) -> Proved:
        return self.modus_ponens(
            self.imp_trans(neg(neg(p)), p, q),
            self.dynamic_inst(self.prop3, {0: p}))

    def dni_l_i(self, pq: Proved) -> Proved:
        p, q = self.get_imp(pq.conclusion)
        return self.modus_ponens(self.dni_l(p, q), pq)

    def dni_r(self, p: Pattern, q: Pattern) -> Proved:
        return self.modus_ponens(
            self.dynamic_inst(self.prop2, {0: p, 1: q, 2: neg(neg(q))}),
            self.imp_provable(p, self.dni(q)))

    def dni_r_i(self, pq: Proved) -> Proved:
        p, q = self.get_imp(pq.conclusion)
        return self.modus_ponens(self.dni_r(p, q), pq)

    def dne_l(self, p: Pattern, q: Pattern) -> Proved:
        return self.modus_ponens(
            self.imp_trans(p, neg(neg(p)), q),
            self.dni(p))

    def dne_l_i(self, pq: Proved) -> Proved:
        p, q = self.get_imp(pq.conclusion)
        return self.modus_ponens(self.dne_l(p, q), pq)

    def dne_r(self, p: Pattern, q: Pattern) -> Proved:
        return self.modus_ponens(
            self.dynamic_inst(self.prop2, {0: p, 1: neg(neg(q)), 2: q}),
            self.imp_provable(p, self.dynamic_inst(self.prop3, {0: q})))

    def dne_r_i(self, pq: Proved) -> Proved:
        p, q = self.get_imp(pq.conclusion)
        return self.modus_ponens(self.dne_r(p, q), pq)

    #    p    q -> r
    # -----------------
    #   (p -> q) -> r
    def helper1(self, p_pf: Proved, qr_pf: Proved) -> Proved:
        p = p_pf.conclusion
        q, r = self.get_imp(qr_pf.conclusion)
        return self.imp_transitivity(
            lambda: self.mpcom(p_pf, q),
            lambda: qr_pf
        )
    
    #     p -> q
    # ---------------
    #   p -> r -> q
    def a1d(self, pq: Proved, r: Pattern) -> Proved:
        pq_conc = pq.conclusion
        assert isinstance(pq_conc, Implication)
        q = pq_conc.right
        return self.imp_transitivity(
            pq,
            self.dynamic_inst(self.prop1, {0:q, 1:r})
        )


    # (p -> q) -> (q -> r) -> p -> r
    def imp_trans(self, p: Pattern, q: Pattern, r: Pattern) -> Proved:
        ...

    # (p -> q) -> (~q -> ~p)
    def con3(self, p: Pattern, q: Pattern) -> Proved:
        return self.imp_trans(p, q, bot)

    # p -> q
    # ----------
    # ~q -> ~p
    def con3_i(self, pq: Proved) -> Proved:
        p, q = self.get_imp(pq.conclusion)
        return self.modus_ponens(
            self.con3(p, q),
            pq
        )

    #      p -> q
    # ----------------
    #   ~q -> p -> r
    def absurd2(self, pq: Proved, r: Pattern) -> Proved:
        p_to_q = pq.conclusion
        assert isinstance(p_to_q, Implication)
        p = p_to_q.left
        q = p_to_q.right
        return self.imp_transitivity(
            lambda: self.dynamic_inst(self.absurd, {0:q, 1:r}),
            lambda: self.modus_ponens(
                self.dynamic_inst(self.imp_trans, {0:p, 1:q, 2:r}),
                pq)
        )

    #   ~p -> q     ~r
    # ------------------
    #   (q -> r) -> p
    def absurd3(self, npq: Proved, nr: Proved) -> Proved:
        ...

    #   p -> ~q
    # ------------------
    #   q -> p -> r
    def absurd4(self, pnq: Proved, r: Pattern) -> Proved:
        pnq_conc = pnq.conclusion
        assert isinstance(pnq_conc, Implication)
        return self.imp_transitivity(
            self.dni(self.get_neg(pnq_conc.right)),
            self.absurd2(pnq, r)
        )

    #   ~p
    # -----------
    #  p -> q
    def absurd_i(self, np: Proved, q: Pattern) -> Proved:
        p = self.get_neg(np.conclusion)
        return self.modus_ponens(
            self.dynamic_inst(self.absurd, {0:p, 1:q}),
            np)

    #   p   ~q
    # -----------
    #  ~(p -> q)
    def and_not_r_intro(self, p: Proved, nq: Proved) -> Proved:
        ...

    # (a -> b)    (c -> d)
    # ---------------------
    # (b -> c) -> (a -> d)
    def imim(self, h1: Proved, h2: Proved) -> Proved:
        ...

    # (a -> b)    (c -> d)
    # ---------------------
    # (b -> c) -> (~~a -> d)
    def imim_nnr(self, h1: Proved, h2: Proved) -> Proved:
        a, _ = self.get_imp(h1.conclusion)
        _, d = self.get_imp(h2.conclusion)
        return self.imp_transitivity(
            self.imim(h1, h2),
            self.modus_ponens(
                self.imp_trans(neg(neg(a)), a, d),
                self.dynamic_inst(self.prop3, {0: a})
            )
        )

    # (a -> b)    (c -> d)
    # ---------------------
    # (~~b -> c) -> (a -> d)
    def imim_nnl(self, h1: Proved, h2: Proved) -> Proved:
        _, b = self.get_imp(h1.conclusion)
        c, _ = self.get_imp(h2.conclusion)
        return self.imp_transitivity(
            self.modus_ponens(
                self.imp_trans(b, neg(neg(b)), c),
                self.dni(b)
            ),
            self.imim(h1, h2)
        )

    # (a -> b)   (c -> d)
    # ---------------------
    # a \/ c -> b \/ d
    def imim_or(self, h1: Proved, h2: Proved) -> Proved:
        return self.imim(
            self.con3_i(h1),
            h2)

    # (a -> b)   (c -> d)
    # ---------------------
    # a /\ c -> b /\ d
    def imim_and(self, h1: Proved, h2: Proved) -> Proved:
        return self.con3_i(self.imim(
            h1,
            self.con3_i(h2)))

    def is_propositional(self, pat: Pattern) -> bool:
        if pat == bot:
            return True
        if isinstance(pat, Implication):
            return self.is_propositional(pat.left) and self.is_propositional(pat.right)
        if isinstance(pat, MetaVar):
            return True
        return False

    # Assumes the input is a propositional formula and transforms it to one
    # made up of only ORs, negations and variables
    # Output is:
    #   the representation of the new term
    #   proof that old term -> new term
    #   proof that new term -> old term
    # NOTE! When the new term is Top or Bottom, we only populate the
    # first proof, leaving the second one as a dummy
    # This proof will be a proof of `old term` or `neg(old term)` respectively
    # (as opposed to, say, `old term -> Top``)
    def to_conj(self, pat: Pattern) -> Tuple[ConjTerm, Proved, Proved]:
        if pat == bot:
            bot_imp_bot = self.imp_refl(bot)
            return ConjBool(False), bot_imp_bot, Proved()
        if pat == top:
            top_imp_top = self.imp_refl(top)
            return ConjBool(True), top_imp_top, Proved()
        match pat:
            case MetaVar(id):
                phi_imp_phi = self.imp_refl(pat)
                return ConjVar(id), phi_imp_phi, phi_imp_phi
            case Implication(phi0, phi1):
                phi1_conj, phi1_l, phi1_r = self.to_conj(phi1)

                if isinstance(phi1_conj, ConjBool):
                    if phi1_conj.negated:
                        pf = self.imp_provable(phi0, phi1_l)
                        return ConjBool(True), pf, Proved()
                    else:
                        #TODO Consider whether it's worth adding a special branch here
                        # to optimize for early construction of AND terms:
                        # if isinstance(phi0, Implication):
                        #     ...
                        phi0_conj, phi0_l, phi0_r = self.to_conj(phi0)
                        if isinstance(phi0_conj, ConjBool):
                            if phi0_conj.negated:
                                pf = self.and_not_r_intro(phi0_l, phi1_l)
                                return ConjBool(False), pf, Proved()
                            else:
                                pf = self.absurd_i(phi0_l, phi1)
                                return ConjBool(True), pf, Proved()
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
                        return ConjBool(True), pf, Proved()
                if phi0_conj.negated:
                    phi0_conj.negated = False
                    return ConjOr(phi0_conj, phi1_conj), self.imim(phi0_r, phi1_l), self.imim(phi0_l, phi1_r)
                else:
                    phi0_conj.negated = True
                    return ConjOr(phi0_conj, phi1_conj), self.imim_nnr(phi0_r, phi1_l), self.imim_nnl(phi0_l, phi1_r)
            case _:
                #TODO Add more context to this error message
                raise AssertionError('Unexpected pattern')

    # Assumes `term` is made up only of OR nodes and vars (+ single negations)
    def propag_neg(self, term:ConjTerm) -> Tuple[ConjTerm, Proved, Proved]:
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
                    pf1 = self.imp_transitivity(
                        lambda: self.con3_i(self.dne_r(a1, b1)),
                        lambda: pf1
                    )
                    a2, nnb2 = self.get_imp(self.get_neg(pf2.conclusion.right))
                    b2 = self.get_neg(self.get_neg(nnb2))
                    pf2 = self.imp_transitivity(
                        lambda: pf2,
                        lambda: self.con3_i(self.dni_r(a2, b2))
                    )
                return ConjAnd(term_l, term_r), pf1, pf2 
            else:
                term_l, term_l_pf1, term_l_pf2 = self.propag_neg(term.left)
                term_r, term_r_pf1, term_r_pf2 = self.propag_neg(term.right)
                return ConjOr(term_l, term_r), self.imim_or(term_l_pf1, term_r_pf1), self.imim_or(term_l_pf2, term_r_pf2)
        else:
            #TODO Add more context to this error message
            raise AssertionError('Unexpected pattern')

