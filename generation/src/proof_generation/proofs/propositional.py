from __future__ import annotations

import sys
from typing import TYPE_CHECKING

from proof_generation.proof import Implication, MetaVar, Mu, ProofExp, SVar

if TYPE_CHECKING:
    from proof_generation.proof import BasicInterpreter, Pattern, PatternExpression, Proved, ProvedExpression

bot = Mu(SVar(0), SVar(0))
phi0 = MetaVar(0)
phi0_implies_phi0 = Implication(phi0, phi0)

def neg(p: Pattern) -> Pattern:
    return Implication(p, bot)

class Propositional(ProofExp):
    def __init__(self, interpreter: BasicInterpreter) -> None:
        super().__init__(interpreter)

    @staticmethod
    def claims() -> list[Pattern]:
        phi0 = MetaVar(0)
        bot = Mu(SVar(0), SVar(0))
        top = Implication(bot, bot)
        neg_phi0 = Implication(phi0, bot)
        return [
            Implication(phi0, phi0),  # Reflexivity
            top,  # Top
            Implication(bot, phi0),  # Bot_elim
            Implication(Implication(neg_phi0, bot), phi0),  # Contradiction
            Implication(Implication(Implication(phi0, bot), phi0), phi0),  # Peirce_bot
        ]

    def claim_expressions(self) -> list[PatternExpression]:
        return [self.phi0_implies_phi0, self.top, self.bot_implies_phi0, self.contradiction_claim, self.peirce_bot_phi0]

    def proof_expressions(self) -> list[ProvedExpression]:
        return [self.imp_reflexivity, self.top_intro, self.bot_elim, self.contradiction_proof, self.peirce_bot]

    # Notation
    # ========

    def phi0(self) -> Pattern:
        if ret := self.load_notation('phi0'):
            return ret
        return self.save_notation('phi0', self.metavar(0))

    def phi0_implies_phi0(self) -> Pattern:
        if ret := self.load_notation('phi0-implies-phi0'):
            return ret
        return self.save_notation('phi0-implies-phi0', self.implies(self.phi0(), self.phi0()))

    def bot(self) -> Pattern:
        if ret := self.load_notation('bot'):
            return ret
        return self.save_notation('bot', self.mu(0, self.svar(0)))

    def neg_notation(self) -> Pattern:
        if ret := self.load_notation('neg'):
            return ret
        return self.save_notation('neg', self.implies(self.phi0(), self.bot()))

    def neg(self, p: PatternExpression) -> Pattern:
        return self.instantiate_notation(self.neg_notation(), {0: p()})

    def top(self) -> Pattern:
        if ret := self.load_notation('top'):
            return ret
        return self.save_notation('top', self.neg(self.bot))

    def neg_phi0(self) -> Pattern:
        if ret := self.load_notation('neg-phi0'):
            return ret
        return self.save_notation('neg-phi0', self.neg(self.phi0))

    def bot_implies_phi0(self) -> Pattern:
        if ret := self.load_notation('bot-implies-phi0'):
            return ret
        return self.save_notation('bot-implies-phi0', self.implies(self.bot(), self.phi0()))

    def contradiction_claim(self) -> Pattern:
        if ret := self.load_notation('contradiction'):
            return ret
        return self.save_notation(
            'contradiction',
            # (neg phi0 -> bot) -> phi0
            self.implies(self.implies(self.neg_phi0(), self.bot()), self.phi0()),
        )

    def peirce_bot_phi0(self) -> Pattern:
        if ret := self.load_notation('peirce-bot'):
            return ret
        return self.save_notation(
            'peirce-bot',
            # (((ph0 -> bot) -> ph0) -> ph0)
            self.implies(self.implies(self.implies(self.phi0(), self.bot()), self.phi0()), self.phi0()),
        )

    # Proofs
    # ======

    # phi0 -> phi0
    def imp_reflexivity(self) -> Proved:
        # fmt: off
        return self.modus_ponens(
            self.modus_ponens(
                self.prop2().instantiate({1: phi0_implies_phi0, 2: phi0}),
                self.prop1().instantiate({1: phi0_implies_phi0}),
            ),
            self.prop1().instantiate({1: phi0}),
        )

    # phi1 -> phi2 and phi2 -> phi3 yields also a proof of phi1 -> phi3
    def imp_transitivity(self, phi0_imp_phi1: Proved, phi1_imp_phi2: Proved) -> Proved:
        phi0_imp_phi1_conc = phi0_imp_phi1.conclusion

        match phi0_imp_phi1_conc:
            case Implication(phi0, phi1):
                pass
            case _:
                raise AssertionError('Expected implication')
        phi1_imp_phi2_conc = phi1_imp_phi2.conclusion
        match phi1_imp_phi2_conc:
            case Implication(phi1_r, phi2):
                assert phi1_r == phi1
            case _:
                raise AssertionError('Expected implication')

        return self.modus_ponens(
            self.modus_ponens(
                self.prop2().instantiate({1: phi1, 2: phi2, 0: MetaVar(0)}),
                self.modus_ponens(self.prop1().instantiate({0: phi1_imp_phi2_conc}), phi1_imp_phi2),
            ).instantiate({1: phi0}),
            phi0_imp_phi1,
        )

    def top_intro(self) -> Proved:
        return self.imp_reflexivity().instantiate({0: bot})

    def bot_elim(self) -> Proved:
        neg_neg_phi0 = neg(neg(phi0))

        return self.modus_ponens(
            # ((bot -> neg neg 0) -> (bot -> 0)))
            self.modus_ponens(
                # (bot -> (neg neg 0 -> 0)) -> ((bot -> neg neg 0) -> (bot -> 0))
                self.prop2().instantiate({0: bot, 1: neg_neg_phi0, 2: phi0}),
                # (bot -> (neg neg 0 -> 0))
                self.modus_ponens(
                    # (neg neg 0 -> 0) -> (bot -> (neg neg 0 -> 0))
                    self.prop1().instantiate({0: Implication(neg_neg_phi0, phi0), 1: bot}),
                    # (neg neg 0 -> 0)
                    self.prop3().instantiate({0: phi0}),
                ),
            ),
            # (bot -> (neg neg phi0))
            self.prop1().instantiate({0: bot, 1: neg(phi0)}),
        )

    # (neg phi0 -> bot) -> phi0
    def contradiction_proof(self) -> Proved:
        return self.prop3().instantiate({0: phi0})

    # (((ph0 -> bot) -> ph0) -> ph0)
    def peirce_bot(self) -> Proved:
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
                self.prop2().instantiate(
                    {
                        # ((ph0 -> bot) -> ph0) = neg 0 -> 0
                        0: phi0_bot_imp_ph0(),
                        # ((ph0 -> bot) -> bot) = neg 0 -> bot
                        1: phi0_bot_imp_bot(),
                        2: phi0,
                    }
                ),
                self.modus_ponens(
                    self.prop1().instantiate(
                        {
                            # (((ph0 -> bot) -> bot) -> ph0)
                            0: Implication(phi0_bot_imp_bot(), phi0),
                            # ((ph0 -> bot) -> ph0)
                            1: phi0_bot_imp_ph0(),
                        }
                    ),
                    # ph0
                    self.prop3().instantiate({0: phi0}),
                ),
            )

        def modus_ponens_2() -> Proved:
            return self.modus_ponens(
                self.prop2().instantiate(
                    {
                        0: phi0_bot_imp_ph0(),
                        1: phi0_bot_imp_phi0_bot(),
                        # (((ph0 -> bot) -> phi0) -> ((ph0 -> bot) -> bot)))
                        2: Implication(phi0_bot_imp_ph0(), phi0_bot_imp_bot()),
                    }
                ),
                self.modus_ponens(
                    self.prop1().instantiate(
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
                        }
                    ),
                    self.prop2().instantiate(
                        {
                            0: Implication(phi0, bot),
                            1: phi0,
                            2: bot,
                        }
                    ),
                ),
            )

        def modus_ponens_3() -> Proved:
            return self.modus_ponens(
                # ((phi0 -> bot) -> (phi0 -> bot)) -> (((phi0 -> bot) -> phi0) -> ((phi0 -> bot) -> (phi0->bot)))
                self.prop1().instantiate(
                    {
                        0: phi0_bot_imp_phi0_bot(),
                        1: phi0_bot_imp_ph0(),
                    }
                ),
                # ((phi0 -> bot) -> phi0) -> ((phi0 -> bot) -> phi0)
                self.imp_reflexivity().instantiate(
                    {
                        # (phi0 -> bot)
                        0: Implication(phi0, bot),
                    }
                ),
            )

        return self.modus_ponens(
            modus_ponens_1(),
            self.modus_ponens(
                self.modus_ponens(
                    self.prop2().instantiate(
                        {
                            0: phi0_bot_imp_ph0(),
                            1: phi0_bot_imp_ph0(),
                            2: phi0_bot_imp_bot(),
                        }
                    ),
                    self.modus_ponens(
                        modus_ponens_2(),
                        modus_ponens_3(),
                    ),
                ),
                self.imp_reflexivity().instantiate({0: phi0_bot_imp_ph0()}),
            ),
        )


if __name__ == '__main__':
    Propositional.main(sys.argv)
