from __future__ import annotations

import sys
from dataclasses import dataclass
from functools import partial
from typing import TYPE_CHECKING

from proof_generation.pattern import Implies, MetaVar, Notation, bot
from proof_generation.proof import ProofExp, ProofThunk, name_proof_dec

if TYPE_CHECKING:
    from proof_generation.basic_interpreter import BasicInterpreter
    from proof_generation.pattern import Pattern

phi0 = MetaVar(0)
phi1 = MetaVar(1)
phi2 = MetaVar(2)


@dataclass(frozen=True, eq=False)
class Negation(Notation):
    phi0: Pattern

    @classmethod
    def definition(cls) -> Pattern:
        return Implies(phi0, bot)

    def __str__(self) -> str:
        return f'¬({str(self.phi0)})'


def neg(p: Pattern) -> Pattern:
    return Negation(p)


@dataclass(frozen=True, eq=False)
class Top(Notation):
    @classmethod
    def definition(cls) -> Pattern:
        return neg(bot)

    def __str__(self) -> str:
        return '⊤'


top = Top()


@dataclass(frozen=True, eq=False)
class And(Notation):
    phi0: Pattern
    phi1: Pattern

    @classmethod
    def definition(cls) -> Pattern:
        return neg(Implies(phi0, neg(phi1)))

    def __str__(self) -> str:
        return f'({self.phi0} ∧ {self.phi1})'


@dataclass(frozen=True, eq=False)
class Or(Notation):
    phi0: Pattern
    phi1: Pattern

    @classmethod
    def definition(cls) -> Pattern:
        return Implies(neg(phi0), phi1)

    def __str__(self) -> str:
        return f'({self.phi0} ∨ {self.phi1})'


@dataclass(frozen=True, eq=False)
class Equiv(Notation):
    phi0: Pattern
    phi1: Pattern

    @classmethod
    def definition(cls) -> Pattern:
        return And(Implies(phi0, phi1), Implies(phi1, phi0))

    def __str__(self) -> str:
        return f'({str(self.phi0)}) <-> ({str(self.phi1)})'


class Propositional(ProofExp):
    def __init__(self, interpreter: BasicInterpreter) -> None:
        super().__init__(interpreter)

    @staticmethod
    def axioms() -> list[Pattern]:
        return []

    @staticmethod
    def claims() -> list[Pattern]:
        return [
            Implies(phi0, phi0),  # Reflexivity
            top,  # Top
            Implies(bot, phi0),  # Bot_elim
            Implies(neg(neg(phi0)), phi0),  # Double Negation elim
            Implies(phi0, neg(neg(phi0))),  # Double Negation intro
            Implies(neg(phi0), Implies(phi0, phi1)),  # Absurd
            Implies(Implies(neg(phi0), phi0), phi0),  # Peirce_bot
            Implies(Implies(phi0, phi1), Implies(Implies(phi1, phi2), Implies(phi0, phi2))),  # Implication Transitivity
        ]

    def proof_expressions(self) -> list[ProofThunk]:
        return [
            self.imp_refl(),
            self.top_intro(),
            self.bot_elim(),
            self.dneg_elim(),
            self.dneg_intro(),
            self.absurd(),
            self.peirce_bot(),
            self.imp_trans(),
        ]

    # Proofs
    # ======

    # NOTE To be used only in a propositional logic context
    def build_subst(self, p: Pattern = phi0, q: Pattern = phi1, r: Pattern = phi2) -> dict[int, Pattern]:
        ret = {}
        if p != phi0:
            ret[0] = p
        if q != phi1:
            ret[1] = q
        if r != phi2:
            ret[2] = r
        return ret

    def load_ax(self, i: int, p: Pattern = phi0, q: Pattern = phi1, r: Pattern = phi2) -> ProofThunk:
        subst = self.build_subst(p, q, r)
        return ProofThunk(
            partial(self.dynamic_inst, partial(self.load_axiom, self.axioms()[i]), subst),
            self.axioms()[i].instantiate(subst),
        )

    def p1(self, p: Pattern = phi0, q: Pattern = phi1) -> ProofThunk:
        return ProofThunk(partial(self.dynamic_inst, self.prop1, self.build_subst(p, q)), Implies(p, Implies(q, p)))

    def p2(self, p: Pattern = phi0, q: Pattern = phi1, r: Pattern = phi2) -> ProofThunk:
        return ProofThunk(
            partial(self.dynamic_inst, self.prop2, self.build_subst(p, q, r)),
            Implies(Implies(p, Implies(q, r)), Implies(Implies(p, q), Implies(p, r))),
        )

    @name_proof_dec
    def dneg_elim(self, p: Pattern = phi0) -> ProofThunk:
        return ProofThunk(partial(self.dynamic_inst, self.prop3, self.build_subst(p)), Implies(neg(neg(p)), p))

    def mp(self, pq_pf: ProofThunk, p_pf: ProofThunk) -> ProofThunk:
        p, q = Implies.extract(pq_pf.conc)
        assert p == p_pf.conc
        return ProofThunk((lambda: self.modus_ponens(pq_pf(), p_pf())), q)

    @name_proof_dec
    def imp_refl(self, p: Pattern = phi0) -> ProofThunk:
        """p -> p"""
        pp = Implies(p, p)
        # fmt: off
        return self.mp(
            self.mp(
                self.p2(p, pp, p),
                self.p1(p, pp)),
            self.p1(p, p))

    def imp_provable(self, p: Pattern, q_pf: ProofThunk) -> ProofThunk:
        """
            q
        ----------
          p -> q
        """
        q = q_pf.conc
        return self.mp(self.p1(q, p), q_pf)

    def imp_transitivity(self, pq_pf: ProofThunk, qr_pf: ProofThunk) -> ProofThunk:
        """
           p -> q    q -> r
        ----------------------
                p -> r
        """
        p, q = Implies.extract(pq_pf.conc)
        q2, r = Implies.extract(qr_pf.conc)
        assert q == q2

        return self.mp(
            # (p -> q) -> (p -> r)
            self.mp(
                # (p -> (q -> r)) -> ((p -> q) -> (p -> r))
                self.p2(p, q, r),
                #  p -> (q -> r)
                self.imp_provable(p, qr_pf),
            ),
            # p -> q
            pq_pf,
        )

    @name_proof_dec
    def top_intro(self) -> ProofThunk:
        """top"""
        return self.imp_refl(bot)

    @name_proof_dec
    def bot_elim(self, p: Pattern = phi0) -> ProofThunk:
        """bot -> p"""
        return self.mp(
            # ((bot -> neg neg p) -> (bot -> p)))
            self.mp(
                # (bot -> (neg neg p -> p)) -> ((bot -> neg neg p) -> (bot -> p))
                self.p2(bot, neg(neg(p)), p),
                #  bot -> (neg neg p -> p)
                self.imp_provable(bot, self.dneg_elim(p)),
            ),
            # (bot -> (neg neg p))
            self.p1(bot, neg(p)),
        )

    def top_imp(self, p_pf: ProofThunk) -> ProofThunk:
        """
            p
        ----------
          T -> p
        """
        return self.imp_provable(top, p_pf)

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
        return self.imp_transitivity(self.p1(q, p), self.mp(self.p2(p, q, r), pf))

    @name_proof_dec
    def dneg_intro(self, p: Pattern = phi0) -> ProofThunk:
        """p -> ~~p"""
        return self.ant_commutativity(self.imp_refl(neg(p)))

    @name_proof_dec
    def absurd(self, p: Pattern = phi0, q: Pattern = phi1) -> ProofThunk:
        """~p -> (p -> q)"""
        return self.mp(
            self.p2(p, bot, q),
            # p -> bot -> q
            self.imp_provable(p, self.bot_elim(q)),
        )

    @name_proof_dec
    def peirce_bot(self, p: Pattern = phi0) -> ProofThunk:
        """(~p -> p) -> p   or, alternatively   p \\/ p -> p"""
        return self.imp_transitivity(self.mp(self.p2(neg(p), p, bot), self.imp_refl(neg(p))), self.dneg_elim(p))

    @name_proof_dec
    def imp_trans(self, p: Pattern = phi0, q: Pattern = phi1, r: Pattern = phi2) -> ProofThunk:
        """(p -> q) -> (q -> r) -> (p -> r)"""
        return self.ant_commutativity(self.imp_transitivity(self.p1(Implies(q, r), p), self.p2(p, q, r)))


if __name__ == '__main__':
    Propositional.main(sys.argv)
