from __future__ import annotations

import sys
from dataclasses import dataclass
from typing import TYPE_CHECKING

from proof_generation.basic_interpreter import BasicInterpreter, ExecutionPhase
from proof_generation.pattern import Implication, MetaVar, Notation, bot, get_imp, is_bot, is_imp, unwrap, unwrap2
from proof_generation.proof import ProofExp

if TYPE_CHECKING:
    from proof_generation.pattern import Pattern
    from proof_generation.proof import ProvedExpression
    from proof_generation.proved import Proved

phi0 = MetaVar(0)
phi1 = MetaVar(1)
phi2 = MetaVar(2)


@dataclass(frozen=True, eq=False)
class Negation(Notation):
    phi0: Pattern

    @staticmethod
    def definition() -> Pattern:
        return Implication(phi0, bot)

    def __str__(self) -> str:
        return f'~({str(self.phi0)})'


def neg(p: Pattern) -> Pattern:
    return Negation(p)


@dataclass(frozen=True, eq=False)
class Top(Notation):
    @staticmethod
    def definition() -> Pattern:
        return neg(bot)

    def __str__(self) -> str:
        return '\u22A4'


top = Top()


@dataclass(frozen=True, eq=False)
class Or(Notation):
    left: Pattern
    right: Pattern

    @staticmethod
    def definition() -> Pattern:
        return Implication(neg(phi0), phi1)

    def __str__(self) -> str:
        return f'({str(self.left)}) \\/ ({str(self.right)})'


def ml_or(l: Pattern, r: Pattern) -> Pattern:
    return Or(l, r)


def is_neg(pat: Pattern) -> Pattern | None:
    if isinstance(pat, Negation):
        return pat.phi0
    if isinstance(pat, Notation):
        return is_neg(pat.conclusion())
    if pat_imp := is_imp(pat):
        if is_bot(pat_imp[1]):
            return pat_imp[0]
        return None
    return None


def get_neg(pat: Pattern) -> Pattern:
    return unwrap(is_neg(pat), 'Expected a negation but got: ' + str(pat) + '\n')


def is_top(pat: Pattern) -> bool:
    if isinstance(pat, Top):
        return True
    if isinstance(pat, Notation):
        return is_top(pat.conclusion())
    if pat_imp := is_imp(pat):
        return is_bot(pat_imp[0]) and is_bot(pat_imp[1])
    return False


def get_top(pat: Pattern) -> None:
    assert is_top(pat), 'Expected Top but instead got: ' + str(pat) + '\n'


def is_or(pat: Pattern) -> tuple[Pattern, Pattern] | None:
    if isinstance(pat, Or):
        return pat.left, pat.right
    if isinstance(pat, Notation):
        return is_or(pat.conclusion())
    if pat_imp := is_imp(pat):
        if l := is_neg(pat_imp[0]):
            return l, pat_imp[1]
        return None
    return None


def get_or(pat: Pattern) -> tuple[Pattern, Pattern]:
    return unwrap2(is_or(pat), 'Expected an Or but got: ' + str(pat) + '\n')


class Propositional(ProofExp):
    def __init__(self, interpreter: BasicInterpreter) -> None:
        super().__init__(interpreter)

    @staticmethod
    def axioms() -> list[Pattern]:
        return []

    @staticmethod
    def claims() -> list[Pattern]:
        return [
            Implication(phi0, phi0),  # Reflexivity
            top,  # Top
            Implication(bot, phi0),  # Bot_elim
            Implication(neg(neg(phi0)), phi0),  # Contradiction
            Implication(neg(phi0), Implication(phi0, phi1)),  # Absurd
            Implication(Implication(neg(phi0), phi0), phi0),  # Peirce_bot
        ]

    def proof_expressions(self) -> list[ProvedExpression]:
        return [
            self.imp_refl,
            self.top_intro,
            self.bot_elim,
            self.contradiction_proof,
            self.absurd,
            self.peirce_bot,
        ]

    # TODO This function should not exist anymore once we
    # have support for Lemmas in the binary format
    def get_conc(self, p: ProvedExpression) -> Pattern:
        i = self.interpreter
        self.interpreter = BasicInterpreter(ExecutionPhase.Proof)
        conc = p().conclusion
        self.interpreter = i
        return conc

    # Proofs
    # ======

    def imp_refl(self, p: Pattern = phi0) -> Proved:
        """p -> p"""
        pp = Implication(p, p)
        # fmt: off
        return self.modus_ponens(
            self.modus_ponens(
                self.dynamic_inst(self.prop2, {0: p, 1: pp, 2: p}),
                self.dynamic_inst(self.prop1, {0: p, 1: pp})),
            self.dynamic_inst(self.prop1, {0: p, 1: p}))

    def imp_provable(self, p: Pattern, q_pf: ProvedExpression) -> Proved:
        """
            q
        ----------
          p -> q
        """
        q = self.get_conc(q_pf)
        return self.modus_ponens(self.dynamic_inst(self.prop1, {0: q, 1: p}), q_pf())

    def imp_transitivity(self, phi0_imp_phi1: ProvedExpression, phi1_imp_phi2: ProvedExpression) -> Proved:
        """
           p -> q    q -> r
        ----------------------
                p -> r
        """
        a, b = get_imp(self.get_conc(phi0_imp_phi1))
        b2, c = get_imp(self.get_conc(phi1_imp_phi2))
        assert b == b2

        return self.modus_ponens(
            # (a -> b) -> (a -> c)
            self.modus_ponens(
                # (a -> (b -> c)) -> ((a -> b) -> (a -> c))
                self.dynamic_inst(self.prop2, {0: a, 1: b, 2: c}),
                #  a -> (b -> c)
                self.imp_provable(a, phi1_imp_phi2),
            ),
            phi0_imp_phi1(),
        )

    def top_intro(self) -> Proved:
        """top"""
        return self.imp_refl(bot)

    def bot_elim(self, p: Pattern = phi0) -> Proved:
        """bot -> p"""
        neg_neg_p = neg(neg(p))

        return self.modus_ponens(
            # ((bot -> neg neg p) -> (bot -> p)))
            self.modus_ponens(
                # (bot -> (neg neg p -> p)) -> ((bot -> neg neg p) -> (bot -> p))
                self.dynamic_inst(self.prop2, {0: bot, 1: neg_neg_p, 2: p}),
                #  bot -> (neg neg p -> p)
                self.imp_provable(bot, lambda: self.dynamic_inst(self.prop3, {0: p})),
            ),
            # (bot -> (neg neg p))
            self.dynamic_inst(self.prop1, {0: bot, 1: neg(p)}),
        )

    def top_imp(self, p_pf: ProvedExpression) -> Proved:
        """
            p
        ----------
          T -> p
        """
        return self.imp_provable(top, p_pf)

    def imp_top(self, p: Pattern) -> Proved:
        """p -> T"""
        return self.imp_provable(p, self.top_intro)

    def contradiction_proof(self) -> Proved:
        """(neg p -> bot) -> p"""
        return self.prop3()

    def absurd(self, a: Pattern = phi0, b: Pattern = phi1) -> Proved:
        """(neg p) -> p -> q"""
        bot_to_b = Implication(bot, b)

        return self.modus_ponens(
            self.dynamic_inst(self.prop2, {0: a, 1: bot, 2: b}),
            # a -> bot -> b
            self.modus_ponens(self.dynamic_inst(self.prop1, {0: bot_to_b, 1: a}), self.bot_elim(b)),
        )

    def peirce_bot(self) -> Proved:
        """(((ph0 -> bot) -> ph0) -> ph0)"""

        def phi0_bot_imp_ph0() -> Pattern:
            # ((ph0 -> bot) -> ph0)
            return Implication(Implication(phi0, bot), phi0)

        def phi0_bot_imp_bot() -> Pattern:
            # (ph0 -> bot) -> bot)
            return Implication(Implication(phi0, bot), bot)

        def phi0_bot_imp_phi0_bot() -> Pattern:
            # (phi0 -> bot) -> (phi0->bot)
            return Implication(Implication(phi0, bot), Implication(phi0, bot))

        def modus_ponens_1() -> Proved:
            return self.modus_ponens(
                self.dynamic_inst(
                    self.prop2,
                    {
                        # ((ph0 -> bot) -> ph0) = neg 0 -> 0
                        0: phi0_bot_imp_ph0(),
                        # ((ph0 -> bot) -> bot) = neg 0 -> bot
                        1: phi0_bot_imp_bot(),
                        2: phi0,
                    },
                ),
                self.modus_ponens(
                    self.dynamic_inst(
                        self.prop1,
                        {
                            # (((ph0 -> bot) -> bot) -> ph0)
                            0: Implication(phi0_bot_imp_bot(), phi0),
                            # ((ph0 -> bot) -> ph0)
                            1: phi0_bot_imp_ph0(),
                        },
                    ),
                    # ph0
                    self.dynamic_inst(self.prop3, {0: phi0}),
                ),
            )

        def modus_ponens_2() -> Proved:
            return self.modus_ponens(
                self.dynamic_inst(
                    self.prop2,
                    {
                        0: phi0_bot_imp_ph0(),
                        1: phi0_bot_imp_phi0_bot(),
                        # (((ph0 -> bot) -> phi0) -> ((ph0 -> bot) -> bot)))
                        2: Implication(phi0_bot_imp_ph0(), phi0_bot_imp_bot()),
                    },
                ),
                self.modus_ponens(
                    self.dynamic_inst(
                        self.prop1,
                        {
                            # ((phi0 -> bot) -> (phi0 -> bot)) -> (((ph0 -> bot) -> phi0) -> ((ph0 -> bot) -> bot))),
                            0: Implication(
                                Implication(
                                    Implication(phi0, bot),
                                    Implication(phi0, bot),
                                ),
                                Implication(
                                    phi0_bot_imp_ph0(),
                                    phi0_bot_imp_bot(),
                                ),
                            ),
                            1: phi0_bot_imp_ph0(),
                        },
                    ),
                    self.dynamic_inst(
                        self.prop2,
                        {
                            0: Implication(phi0, bot),
                            1: phi0,
                            2: bot,
                        },
                    ),
                ),
            )

        def modus_ponens_3() -> Proved:
            return self.modus_ponens(
                # ((phi0 -> bot) -> (phi0 -> bot)) -> (((phi0 -> bot) -> phi0) -> ((phi0 -> bot) -> (phi0->bot)))
                self.dynamic_inst(
                    self.prop1,
                    {
                        0: phi0_bot_imp_phi0_bot(),
                        1: phi0_bot_imp_ph0(),
                    },
                ),
                # ((phi0 -> bot) -> phi0) -> ((phi0 -> bot) -> phi0)
                self.imp_refl(Implication(phi0, bot)),
            )

        return self.modus_ponens(
            modus_ponens_1(),
            self.modus_ponens(
                self.modus_ponens(
                    self.dynamic_inst(
                        self.prop2,
                        {
                            0: phi0_bot_imp_ph0(),
                            1: phi0_bot_imp_ph0(),
                            2: phi0_bot_imp_bot(),
                        },
                    ),
                    self.modus_ponens(
                        modus_ponens_2(),
                        modus_ponens_3(),
                    ),
                ),
                self.imp_refl(phi0_bot_imp_ph0()),
            ),
        )


if __name__ == '__main__':
    Propositional.main(sys.argv)
