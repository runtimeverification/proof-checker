from __future__ import annotations

import sys
from typing import TYPE_CHECKING

from proof_generation.pattern import Implies, MetaVar, _and, _or, bot, equiv, neg, phi0, phi1, phi2, top
from proof_generation.proof import ProofExp

if TYPE_CHECKING:
    from proof_generation.pattern import Pattern
    from proof_generation.proof import ProofThunk


PROPOSITIONAL_NOTATIONS = (bot, neg, top, _and, _or, equiv)


def _build_subst(pats: list[Pattern]) -> dict[int, Pattern]:
    ret = {}
    for i, p in enumerate(pats):
        if p != MetaVar(i):
            ret[i] = p
    return ret


class Propositional(ProofExp):
    def __init__(self) -> None:
        super().__init__(
            axioms=[],
            notations=list(PROPOSITIONAL_NOTATIONS),
            claims=[
                Implies(phi0, phi0),  # Reflexivity
                top(),  # Top
                Implies(bot(), phi0),  # Bot_elim
                Implies(neg(neg(phi0)), phi0),  # Double Negation elim
                Implies(phi0, neg(neg(phi0))),  # Double Negation intro
                Implies(neg(phi0), Implies(phi0, phi1)),  # Absurd
                Implies(Implies(neg(phi0), phi0), phi0),  # Peirce_bot
                Implies(
                    Implies(phi0, phi1), Implies(Implies(phi1, phi2), Implies(phi0, phi2))
                ),  # Implication Transitivity
            ],
            proof_expressions=[
                self.imp_refl(),
                self.top_intro(),
                self.bot_elim(),
                self.dneg_elim(),
                self.dneg_intro(),
                self.absurd(),
                self.peirce_bot(),
                self.imp_trans(),
            ],
        )

    # Proofs
    # ======

    def prop1_inst(self, p: Pattern = phi0, q: Pattern = phi1) -> ProofThunk:
        return self.dynamic_inst(self.prop1(), _build_subst([p, q]))

    def prop2_inst(self, p: Pattern = phi0, q: Pattern = phi1, r: Pattern = phi2) -> ProofThunk:
        return self.dynamic_inst(self.prop2(), _build_subst([p, q, r]))

    def dneg_elim(self, p: Pattern = phi0) -> ProofThunk:
        return self.dynamic_inst(self.prop3(), _build_subst([p]))

    def imp_refl(self, p: Pattern = phi0) -> ProofThunk:
        """p -> p"""
        pp = Implies(p, p)
        # fmt: off
        return self.modus_ponens(
            self.modus_ponens(
                self.prop2_inst(p, pp, p),
                self.prop1_inst(p, pp)),
            self.prop1_inst(p, p))

    def imp_provable(self, p: Pattern, q_pf: ProofThunk) -> ProofThunk:
        """
            q
        ----------
          p -> q
        """
        q = q_pf.conc
        return self.modus_ponens(self.prop1_inst(q, p), q_pf)

    def imp_transitivity(self, pq_pf: ProofThunk, qr_pf: ProofThunk) -> ProofThunk:
        """
           p -> q    q -> r
        ----------------------
                p -> r
        """
        p, q = Implies.extract(pq_pf.conc)
        q2, r = Implies.extract(qr_pf.conc)
        assert q == q2

        return self.modus_ponens(
            # (p -> q) -> (p -> r)
            self.modus_ponens(
                # (p -> (q -> r)) -> ((p -> q) -> (p -> r))
                self.prop2_inst(p, q, r),
                #  p -> (q -> r)
                self.imp_provable(p, qr_pf),
            ),
            # p -> q
            pq_pf,
        )

    def top_intro(self) -> ProofThunk:
        """top"""
        return self.imp_refl(bot())

    def bot_elim(self, p: Pattern = phi0) -> ProofThunk:
        """bot -> p"""
        return self.modus_ponens(
            # ((bot -> neg neg p) -> (bot -> p)))
            self.modus_ponens(
                # (bot -> (neg neg p -> p)) -> ((bot -> neg neg p) -> (bot -> p))
                self.prop2_inst(bot(), neg(neg(p)), p),
                #  bot -> (neg neg p -> p)
                self.imp_provable(bot(), self.dneg_elim(p)),
            ),
            # (bot -> (neg neg p))
            self.prop1_inst(bot(), neg(p)),
        )

    def top_imp(self, p_pf: ProofThunk) -> ProofThunk:
        """
            p
        ----------
          T -> p
        """
        return self.imp_provable(top(), p_pf)

    def imp_top(self, p: Pattern) -> ProofThunk:
        """p -> T"""
        return self.imp_provable(p, self.top_intro())

    def ant_commutativity(self, pf: ProofThunk) -> ProofThunk:
        """
          p -> (q -> r)
        ---------------
          q -> (p -> r)
        """
        p, qr = Implies.extract(pf.conc)
        q, r = Implies.extract(qr)
        return self.imp_transitivity(self.prop1_inst(q, p), self.modus_ponens(self.prop2_inst(p, q, r), pf))

    def dneg_intro(self, p: Pattern = phi0) -> ProofThunk:
        """p -> ~~p"""
        return self.ant_commutativity(self.imp_refl(neg(p)))

    def absurd(self, p: Pattern = phi0, q: Pattern = phi1) -> ProofThunk:
        """~p -> (p -> q)"""
        return self.modus_ponens(
            self.prop2_inst(p, bot(), q),
            # p -> bot -> q
            self.imp_provable(p, self.bot_elim(q)),
        )

    def peirce_bot(self, p: Pattern = phi0) -> ProofThunk:
        """(~p -> p) -> p   or, alternatively   p \\/ p -> p"""
        return self.imp_transitivity(
            self.modus_ponens(self.prop2_inst(neg(p), p, bot()), self.imp_refl(neg(p))), self.dneg_elim(p)
        )

    def imp_trans(self, p: Pattern = phi0, q: Pattern = phi1, r: Pattern = phi2) -> ProofThunk:
        """(p -> q) -> (q -> r) -> (p -> r)"""
        return self.ant_commutativity(
            self.imp_transitivity(self.prop1_inst(Implies(q, r), p), self.prop2_inst(p, q, r))
        )

    def mpcom(self, p_pf: ProofThunk, q: Pattern) -> ProofThunk:
        """
               p
        -----------------
          (p -> q) -> q
        """
        p = p_pf.conc
        pq = Implies(p, q)
        return self.modus_ponens(
            self.modus_ponens(self.prop2_inst(pq, p, q), self.imp_refl(pq)), self.imp_provable(pq, p_pf)
        )

    def dni_l(self, p: Pattern, q: Pattern) -> ProofThunk:
        """(p -> q) -> (~~p -> q)"""
        return self.modus_ponens(self.imp_trans(neg(neg(p)), p, q), self.dneg_elim(p))

    def dni_l_i(self, pq_pf: ProofThunk) -> ProofThunk:
        """
            p -> q
        --------------
          ~~p -> q
        """
        p, q = Implies.extract(pq_pf.conc)
        return self.modus_ponens(self.dni_l(p, q), pq_pf)

    def dni_r(self, p: Pattern, q: Pattern) -> ProofThunk:
        """(p -> q) -> (p -> ~~q)"""
        return self.modus_ponens(self.prop2_inst(p, q, neg(neg(q))), self.imp_provable(p, self.dneg_intro(q)))

    def dni_r_i(self, pq_pf: ProofThunk) -> ProofThunk:
        """
           p -> q
        --------------
          p -> ~~q
        """
        p, q = Implies.extract(pq_pf.conc)
        return self.modus_ponens(self.dni_r(p, q), pq_pf)

    def dne_l(self, p: Pattern, q: Pattern) -> ProofThunk:
        """(~~p -> q) -> (p -> q)"""
        return self.modus_ponens(self.imp_trans(p, neg(neg(p)), q), self.dneg_intro(p))

    def dne_l_i(self, pq_pf: ProofThunk) -> ProofThunk:
        """
          ~~p -> q
        --------------
            p -> q
        """
        p, q = Implies.extract(pq_pf.conc)
        return self.modus_ponens(self.dne_l(p, q), pq_pf)

    def dne_r(self, p: Pattern, q: Pattern) -> ProofThunk:
        """(p -> ~~q) -> (p -> q)"""
        return self.modus_ponens(self.prop2_inst(p, neg(neg(q)), q), self.imp_provable(p, self.dneg_elim(q)))

    def dne_r_i(self, pq_pf: ProofThunk) -> ProofThunk:
        """
          p -> ~~q
        --------------
           p -> q
        """
        p, q = Implies.extract(pq_pf.conc)
        return self.modus_ponens(self.dne_r(p, q), pq_pf)

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
        return self.imp_transitivity(pq_pf, self.prop1_inst(q, r))

    def con3(self, p: Pattern, q: Pattern) -> ProofThunk:
        """(p -> q) -> (~q -> ~p)"""
        return self.imp_trans(p, q, bot())

    def con3_i(self, pq_pf: ProofThunk) -> ProofThunk:
        """
          p -> q
        ------------
          ~q -> ~p
        """
        p, q = Implies.extract(pq_pf.conc)
        return self.modus_ponens(self.con3(p, q), pq_pf)

    def absurd2(self, pq_pf: ProofThunk, r: Pattern) -> ProofThunk:
        """
             p -> q
        -----------------
           ~q -> p -> r
        """
        p, q = Implies.extract(pq_pf.conc)
        return self.imp_transitivity(self.absurd(q, r), self.modus_ponens(self.imp_trans(p, q, r), pq_pf))

    def lemma1(self, q: Pattern, pf: ProofThunk) -> ProofThunk:
        """
                ~p
        ------------------
          (q -> p) -> ~q
        """
        p = neg.assert_matches(pf.conc)[0]
        return self.modus_ponens(self.prop2_inst(q, p, bot()), self.imp_provable(q, pf))

    def con1(self, pf: ProofThunk) -> ProofThunk:
        """
          ~p -> q
        -----------
          ~q -> p
        """
        np, q = Implies.extract(pf.conc)
        p = neg.assert_matches(np)[0]
        return self.imp_transitivity(
            self.modus_ponens(
                self.ant_commutativity(
                    self.imp_transitivity(self.prop1_inst(neg(q), np), self.prop2_inst(np, q, bot()))
                ),
                pf,
            ),
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
        q = neg.assert_matches(nq)[0]
        return self.imp_transitivity(self.dneg_intro(q), self.absurd2(pnq_pf, r))

    def absurd_i(self, np_pf: ProofThunk, q: Pattern) -> ProofThunk:
        """
           ~p
        -----------
          p -> q
        """
        p = neg.assert_matches(np_pf.conc)[0]
        return self.modus_ponens(self.absurd(p, q), np_pf)

    def and_not_r_intro(self, p_pf: ProofThunk, nq_pf: ProofThunk) -> ProofThunk:
        """
           p   ~q
        -------------
          ~(p -> q)
        """
        p_pf.conc
        q = neg.assert_matches(nq_pf.conc)[0]
        return self.imp_transitivity(self.mpcom(p_pf, q), nq_pf)

    def imim_l(self, pat: Pattern, h: ProofThunk) -> ProofThunk:
        """
              a -> b
        ---------------------
        (b -> c) -> (a -> c)
        """
        a, b = Implies.extract(h.conc)
        return self.modus_ponens(self.imp_trans(a, b, pat), h)

    def imim(self, h1: ProofThunk, h2: ProofThunk) -> ProofThunk:
        """
        (a -> b)    (c -> d)
        ---------------------
        (b -> c) -> (a -> d)
        """
        a, b = Implies.extract(h1.conc)
        c, d = Implies.extract(h2.conc)
        return self.imp_transitivity(
            self.imim_l(c, h1), self.modus_ponens(self.prop2_inst(a, c, d), self.imp_provable(a, h2))
        )

    def imim_r(self, c: Pattern, h: ProofThunk) -> ProofThunk:
        """
              (a -> b)
        ---------------------
        (c -> a) -> (c -> b)
        """
        a, b = Implies.extract(h.conc)
        return self.imim(self.imp_refl(c), h)

    def con2(self, p: Pattern = phi0, q: Pattern = phi1) -> ProofThunk:
        """(p -> ~q) -> (q -> ~p)"""
        return self.imp_transitivity(self.prop2_inst(p, q, bot()), self.imim_l(neg(p), self.prop1_inst(q, p)))

    def imim_nnr(self, h1: ProofThunk, h2: ProofThunk) -> ProofThunk:
        """
        (a -> b)    (c -> d)
        ---------------------
        (b -> c) -> (~~a -> d)
        """
        a, b = Implies.extract(h1.conc)
        c, d = Implies.extract(h2.conc)
        return self.imp_transitivity(
            self.imim(h1, h2), self.modus_ponens(self.imp_trans(neg(neg(a)), a, d), self.dneg_elim(a))
        )

    def imim_nnl(self, h1: ProofThunk, h2: ProofThunk) -> ProofThunk:
        """
        (a -> b)    (c -> d)
        ---------------------
        (~~b -> c) -> (a -> d)
        """
        a, b = Implies.extract(h1.conc)
        c, d = Implies.extract(h2.conc)
        return self.imp_transitivity(
            self.modus_ponens(self.imp_trans(b, neg(neg(b)), c), self.dneg_intro(b)), self.imim(h1, h2)
        )

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
        return self.imp_transitivity(self.mpcom(p_pf, neg(q)), self.modus_ponens(self.dneg_intro(q), q_pf))

    def and_l_imp(self, p: Pattern = phi0, q: Pattern = phi1) -> ProofThunk:
        """p /\\ q -> p"""
        return self.con1(self.absurd(p, neg(q)))

    def and_l(self, pq_pf: ProofThunk) -> ProofThunk:
        """
           p /\\ q
        ------------
              p
        """
        p, q = _and.assert_matches(pq_pf.conc)
        return self.modus_ponens(self.and_l_imp(p, q), pq_pf)

    def and_r_imp(self, p: Pattern = phi0, q: Pattern = phi1) -> ProofThunk:
        """p /\\ q -> q"""
        return self.con1(self.prop1_inst(neg(q), p))

    def and_r(self, pq_pf: ProofThunk) -> ProofThunk:
        """
           p /\\ q
        ------------
              q
        """
        p, q = _and.assert_matches(pq_pf.conc)
        return self.modus_ponens(self.and_r_imp(p, q), pq_pf)


if __name__ == '__main__':
    Propositional().main(sys.argv)
