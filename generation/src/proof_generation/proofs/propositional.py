from __future__ import annotations

import sys
from dataclasses import dataclass
from typing import TYPE_CHECKING

from proof_generation.pattern import Implies, MetaVar, Notation, bot, phi0, phi1, phi2
from proof_generation.proof import ProofExp

if TYPE_CHECKING:
    from proof_generation.basic_interpreter import BasicInterpreter
    from proof_generation.pattern import Pattern
    from proof_generation.proof import ProofThunk


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

    def _build_subst(self, pats: list[Pattern]) -> dict[int, Pattern]:
        ret = {}
        for i, p in enumerate(pats):
            if p != MetaVar(i):
                ret[i] = p
        return ret

    def load_ax(self, i: int) -> ProofThunk:
        return self.load_axiom(self.axioms()[i])

    def prop1_inst(self, p: Pattern = phi0, q: Pattern = phi1) -> ProofThunk:
        return self.dynamic_inst(self.prop1(), self._build_subst([p, q]))

    def prop2_inst(self, p: Pattern = phi0, q: Pattern = phi1, r: Pattern = phi2) -> ProofThunk:
        return self.dynamic_inst(self.prop2(), self._build_subst([p, q, r]))

    def dneg_elim(self, p: Pattern = phi0) -> ProofThunk:
        return self.dynamic_inst(self.prop3(), self._build_subst([p]))

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
        return self.imp_refl(bot)

    def bot_elim(self, p: Pattern = phi0) -> ProofThunk:
        """bot -> p"""
        return self.modus_ponens(
            # ((bot -> neg neg p) -> (bot -> p)))
            self.modus_ponens(
                # (bot -> (neg neg p -> p)) -> ((bot -> neg neg p) -> (bot -> p))
                self.prop2_inst(bot, neg(neg(p)), p),
                #  bot -> (neg neg p -> p)
                self.imp_provable(bot, self.dneg_elim(p)),
            ),
            # (bot -> (neg neg p))
            self.prop1_inst(bot, neg(p)),
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
        return self.imp_transitivity(self.prop1_inst(q, p), self.modus_ponens(self.prop2_inst(p, q, r), pf))

    def dneg_intro(self, p: Pattern = phi0) -> ProofThunk:
        """p -> ~~p"""
        return self.ant_commutativity(self.imp_refl(neg(p)))

    def absurd(self, p: Pattern = phi0, q: Pattern = phi1) -> ProofThunk:
        """~p -> (p -> q)"""
        return self.modus_ponens(
            self.prop2_inst(p, bot, q),
            # p -> bot -> q
            self.imp_provable(p, self.bot_elim(q)),
        )

    def peirce_bot(self, p: Pattern = phi0) -> ProofThunk:
        """(~p -> p) -> p   or, alternatively   p \\/ p -> p"""
        return self.imp_transitivity(
            self.modus_ponens(self.prop2_inst(neg(p), p, bot), self.imp_refl(neg(p))), self.dneg_elim(p)
        )

    def imp_trans(self, p: Pattern = phi0, q: Pattern = phi1, r: Pattern = phi2) -> ProofThunk:
        """(p -> q) -> (q -> r) -> (p -> r)"""
        return self.ant_commutativity(
            self.imp_transitivity(self.prop1_inst(Implies(q, r), p), self.prop2_inst(p, q, r))
        )


if __name__ == '__main__':
    Propositional.main(sys.argv)
