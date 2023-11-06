from __future__ import annotations

from typing import TYPE_CHECKING

from proof_generation.pattern import Implies, MetaVar, Notation, match_single, phi0, phi1, phi2
from proof_generation.proof import ProofExp
from proof_generation.proofs.propositional import And, Equiv, Or, Propositional, bot, neg, top

if TYPE_CHECKING:
    from proof_generation.basic_interpreter import BasicInterpreter
    from proof_generation.pattern import Pattern
    from proof_generation.proof import ProofThunk

### Helper types ###

# The following represents a right-associated disjunction of
# metavariables with the id's in the list. Negative id's represent
# negated metavars. The disjunction is not Bottom terminated.
Clause = list[int]

# Conjunction of right-associated clauses, not Top terminated
ClauseConjunction = list[Clause]


# Structure of Conjunctive Form Tree
class ConjForm:
    negated: bool

    def __init__(self, negated: bool):
        self.negated = negated

    def __str__(self) -> str:
        return str(conj_to_pattern(self))


class CFAnd(ConjForm):
    left: ConjForm
    right: ConjForm

    def __init__(self, left: ConjForm, right: ConjForm):
        super().__init__(False)
        self.left = left
        self.right = right


class CFOr(ConjForm):
    left: ConjForm
    right: ConjForm

    def __init__(self, left: ConjForm, right: ConjForm):
        super().__init__(False)
        self.left = left
        self.right = right


class CFBot(ConjForm):
    pass


class CFVar(ConjForm):
    id: int

    def __init__(self, id: int):
        super().__init__(False)
        self.id = id


def conj_to_pattern(term: ConjForm) -> Pattern:
    pat: Pattern
    if isinstance(term, CFBot):
        pat = bot
    elif isinstance(term, CFVar):
        pat = MetaVar(term.id)
    elif isinstance(term, CFOr):
        pat = Or(conj_to_pattern(term.left), conj_to_pattern(term.right))
    elif isinstance(term, CFAnd):
        pat = And(conj_to_pattern(term.left), conj_to_pattern(term.right))
    if term.negated:
        pat = neg(pat)
    return pat


def clause_to_pattern(l: Clause) -> Pattern:
    assert len(l) > 0
    assert l[0] != 0
    if l[0] < 0:
        pat = neg(MetaVar(-(l[0] + 1)))
    else:
        pat = MetaVar(l[0] - 1)
    if len(l) > 1:
        pat = Or(pat, clause_to_pattern(l[1:]))
    return pat


def clause_list_to_pattern(l: ClauseConjunction) -> Pattern:
    assert len(l) > 0
    pat = clause_to_pattern(l[0])
    if len(l) > 1:
        pat = And(pat, clause_list_to_pattern(l[1:]))
    return pat


class Tautology(ProofExp):
    prop: Propositional

    def __init__(self, interpreter: BasicInterpreter) -> None:
        super().__init__(interpreter)
        self.prop = Propositional(interpreter)

    @staticmethod
    def claims() -> list[Pattern]:
        return []

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
            Equiv(Or(phi0, phi1), Or(phi1, phi0)),
        ]

    def imp_trans_match1(self, h1: ProofThunk, h2: ProofThunk) -> ProofThunk:
        """Same as imp_transitivity but h1 is instantiated to match h2"""
        _, b = Implies.extract(h1.conc)
        c, _ = Implies.extract(h2.conc)
        subst = match_single(b, c, {})
        assert subst is not None
        actual_subst: dict[int, Pattern] = subst
        return self.prop.imp_transitivity(self.dynamic_inst(h1, actual_subst), h2)

    def imp_trans_match2(self, h1: ProofThunk, h2: ProofThunk) -> ProofThunk:
        """Same as imp_transitivity but h2 is instantiated to match h1"""
        _, b = Implies.extract(h1.conc)
        c, _ = Implies.extract(h2.conc)
        subst = match_single(c, b, {})
        assert subst is not None
        actual_subst: dict[int, Pattern] = subst
        return self.prop.imp_transitivity(h1, self.dynamic_inst(h2, actual_subst))

    def and_assoc_r(self, pat1: Pattern = phi0, pat2: Pattern = phi1, pat3: Pattern = phi2) -> ProofThunk:
        """(a /\\ b) /\\ c -> a /\\ (b /\\ c)"""
        return self.prop.load_ax_inst(0, [pat1, pat2, pat3])

    def and_assoc_l(self, pat1: Pattern = phi0, pat2: Pattern = phi1, pat3: Pattern = phi2) -> ProofThunk:
        """a /\\ (b /\\ c) -> (a /\\ b) /\\ c"""
        return self.prop.load_ax_inst(1, [pat1, pat2, pat3])

    def or_assoc_r(self, pat1: Pattern = phi0, pat2: Pattern = phi1, pat3: Pattern = phi2) -> ProofThunk:
        """(a \\/ b) \\/ c -> a \\/ (b \\/ c)"""
        return self.prop.load_ax_inst(2, [pat1, pat2, pat3])

    def or_assoc_l(self, pat1: Pattern = phi0, pat2: Pattern = phi1, pat3: Pattern = phi2) -> ProofThunk:
        """a \\/ (b \\/ c) -> (a \\/ b) \\/ c"""
        return self.prop.load_ax_inst(3, [pat1, pat2, pat3])

    def or_distr_r(self, pat1: Pattern = phi0, pat2: Pattern = phi1, pat3: Pattern = phi2) -> ProofThunk:
        """(a /\\ b) \\/ c -> (a \\/ c) /\\ (b \\/ c)"""
        return self.prop.load_ax_inst(4, [pat1, pat2, pat3])

    def or_distr_r_rev(self, pat1: Pattern = phi0, pat2: Pattern = phi1, pat3: Pattern = phi2) -> ProofThunk:
        """(a \\/ c) /\\ (b \\/ c) -> (a /\\ b) \\/ c"""
        return self.prop.load_ax_inst(5, [pat1, pat2, pat3])

    def or_distr_l(self, pat1: Pattern = phi0, pat2: Pattern = phi1, pat3: Pattern = phi2) -> ProofThunk:
        """a \\/ (b /\\ c) -> (a \\/ b) /\\ (a \\/ c)"""
        return self.prop.load_ax_inst(6, [pat1, pat2, pat3])

    def or_distr_l_rev(self, pat1: Pattern = phi0, pat2: Pattern = phi1, pat3: Pattern = phi2) -> ProofThunk:
        """(a \\/ b) /\\ (a \\/ c) -> a \\/ (b /\\ c)"""
        return self.prop.load_ax_inst(7, [pat1, pat2, pat3])

    def and_assoc(self, pat1: Pattern = phi0, pat2: Pattern = phi1, pat3: Pattern = phi2) -> ProofThunk:
        """a /\\ (b /\\ c) <-> (a /\\ b) /\\ c"""
        return self.prop.and_intro(self.and_assoc_l(pat1, pat2, pat3), self.and_assoc_r(pat1, pat2, pat3))

    def or_assoc(self, pat1: Pattern = phi0, pat2: Pattern = phi1, pat3: Pattern = phi2) -> ProofThunk:
        """a \\/ (b \\/ c) <-> (a \\/ b) \\/ c"""
        return self.prop.and_intro(self.or_assoc_l(pat1, pat2, pat3), self.or_assoc_r(pat1, pat2, pat3))

    def and_comm(self, p: Pattern = phi0, q: Pattern = phi1) -> ProofThunk:
        """p /\\ q <-> q /\\ p"""
        return self.prop.load_ax_inst(8, [p, q])

    def or_comm(self, p: Pattern = phi0, q: Pattern = phi1) -> ProofThunk:
        """p \\/ q <-> q \\/ p"""
        return self.prop.load_ax_inst(9, [p, q])

    def equiv_refl(self, p: Pattern = phi0) -> ProofThunk:
        """p <-> p"""
        pf = self.prop.imp_refl(p)
        return self.prop.and_intro(pf, pf)

    def equiv_sym(self, pf: ProofThunk) -> ProofThunk:
        """
          p <-> q
        -----------
          q <-> p
        """
        return self.prop.and_intro(self.prop.and_r(pf), self.prop.and_l(pf))

    def equiv_transitivity(self, pq_pf: ProofThunk, qr_pf: ProofThunk) -> ProofThunk:
        """
           p <-> q    q <-> r
        ----------------------
                p <-> r
        """
        return self.prop.and_intro(
            self.prop.imp_transitivity(self.prop.and_l(pq_pf), self.prop.and_l(qr_pf)),
            self.prop.imp_transitivity(self.prop.and_r(qr_pf), self.prop.and_r(pq_pf)),
        )

    def equiv_trans_match1(self, h1: ProofThunk, h2: ProofThunk) -> ProofThunk:
        """Same as equiv_transitivity but h1 is instantiated to match h2"""
        _, b = Equiv.extract(h1.conc)
        c, _ = Equiv.extract(h2.conc)
        subst = match_single(b, c, {})
        assert subst is not None
        actual_subst: dict[int, Pattern] = subst
        return self.equiv_transitivity(self.prop.dynamic_inst(h1, actual_subst), h2)

    def equiv_trans_match2(self, h1: ProofThunk, h2: ProofThunk) -> ProofThunk:
        """Same as equiv_transitivity but h2 is instantiated to match h1"""
        _, b = Equiv.extract(h1.conc)
        c, _ = Equiv.extract(h2.conc)
        subst = match_single(c, b, {})
        assert subst is not None
        actual_subst: dict[int, Pattern] = subst
        return self.equiv_transitivity(
            h1,
            self.prop.dynamic_inst(h2, actual_subst),
        )

    def and_cong(self, pf1: ProofThunk, pf2: ProofThunk) -> ProofThunk:
        return self.prop.and_intro(
            self.prop.imim_and(self.prop.and_l(pf1), self.prop.and_l(pf2)),
            self.prop.imim_and(self.prop.and_r(pf1), self.prop.and_r(pf2)),
        )

    def or_cong(self, pf1: ProofThunk, pf2: ProofThunk) -> ProofThunk:
        return self.prop.and_intro(
            self.prop.imim_or(self.prop.and_l(pf1), self.prop.and_l(pf2)),
            self.prop.imim_or(self.prop.and_r(pf1), self.prop.and_r(pf2)),
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

    # TODO Maybe refactor this code to only return a single ProofThunk
    # representing the conjunction of the two, but note that this may
    # come at a cost to performance, since you have to pack and unpack
    # conjunctions repeatedly
    def to_conj_form(self, pat: Pattern) -> tuple[ConjForm, ProofThunk, ProofThunk | None]:
        """
        Assumes the input is a propositional formula and transforms it to one
        made up of only ORs, negations and variables
        Output is:
          the representation of the new pattern
          proof that pat -> new pat
          proof that new pat -> pat
        NOTE! When the new term is Top or Bottom, we only populate the
        first proof; this proof will be a proof of `pat` or `neg(pat)`
        respectively (as opposed to, say, `pat -> Top``)
        """
        if pat == bot:
            return CFBot(False), self.prop.top_intro(), None
        if pat == top:
            return CFBot(True), self.prop.top_intro(), None
        if isinstance(pat, MetaVar):
            phi_imp_phi = self.prop.imp_refl(pat)
            return CFVar(pat.name), phi_imp_phi, phi_imp_phi
        elif pat_imp := Implies.extract(pat):
            pat0 = pat_imp[0]
            pat1 = pat_imp[1]
            pat1_conj, pat1_l, pat1_r = self.to_conj_form(pat1)

            if isinstance(pat1_conj, CFBot):
                if pat1_conj.negated:
                    pf = self.prop.imp_provable(pat0, pat1_l)
                    return CFBot(True), pf, None
                else:
                    pat0_conj, pat0_l, pat0_r = self.to_conj_form(pat0)
                    if isinstance(pat0_conj, CFBot):
                        if pat0_conj.negated:
                            pf = self.prop.and_not_r_intro(pat0_l, pat1_l)
                            return CFBot(False), pf, None
                        else:
                            pf = self.prop.absurd_i(pat0_l, pat1)
                            return CFBot(True), pf, None
                    if pat0_conj.negated:
                        pat0_conj.negated = False
                        assert pat0_r is not None
                        actual_pat0_r: ProofThunk = pat0_r
                        return (
                            pat0_conj,
                            self.prop.absurd3(actual_pat0_r, pat1_l),
                            self.prop.absurd4(pat0_l, pat1),
                        )
                    else:
                        pat0_conj.negated = True
                        assert pat0_r is not None
                        actual_pat0_r = pat0_r
                        return (
                            pat0_conj,
                            self.prop.imim(actual_pat0_r, pat1_l),
                            self.prop.absurd2(pat0_l, pat1),
                        )
            pat0_conj, pat0_l, pat0_r = self.to_conj_form(pat0)
            if isinstance(pat0_conj, CFBot):
                if pat0_conj.negated:
                    assert pat1_r is not None
                    actual_pat1_r: ProofThunk = pat1_r
                    return pat1_conj, self.prop.helper1(pat0_l, pat1_l), self.prop.a1d(actual_pat1_r, pat0)
                else:
                    pf = self.prop.absurd_i(pat0_l, pat1)
                    return CFBot(True), pf, None
            assert pat0_r is not None
            actual_pat0_r = pat0_r
            assert pat1_r is not None
            actual_pat1_r = pat1_r
            if pat0_conj.negated:
                pat0_conj.negated = False
                return (
                    CFOr(pat0_conj, pat1_conj),
                    self.prop.imim(actual_pat0_r, pat1_l),
                    self.prop.imim(pat0_l, actual_pat1_r),
                )
            else:
                pat0_conj.negated = True
                return (
                    CFOr(pat0_conj, pat1_conj),
                    self.prop.imim_nnr(actual_pat0_r, pat1_l),
                    self.prop.imim_nnl(pat0_l, actual_pat1_r),
                )
        else:
            raise AssertionError(f'Unexpected pattern! Expected a propositional pattern but got:\n{str(pat)}\n')
