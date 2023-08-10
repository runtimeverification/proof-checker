#![deny(warnings)]
#![no_std]

extern crate alloc;
use alloc::rc::Rc;
use alloc::vec;
use alloc::vec::Vec;

/// Instructions
/// ============
///
/// Instructions are used to define the on-the-wire representation of matching
/// logic proofs.

#[rustfmt::skip]
#[derive(Debug, Eq, PartialEq)]
pub enum Instruction {
    List = 1,
    // Patterns
    EVar, SVar, Symbol, Implication, Application, Mu, Exists,
    // Meta Patterns,
    MetaVar, ESubst, SSubst,
    // Axiom Schemas,
    Prop1, Prop2, Prop3, Quantifier, PropagationOr, PropagationExists,
    PreFixpoint, Existance, Singleton,
    // Inference rules,
    ModusPonens, Generalization, Frame, Substitution, KnasterTarski,
    // Meta Incference rules,
    Instantiate,
    // Stack Manipulation,
    Pop,
    // Memory Manipulation,
    Save, Load,
    // Journal Manipulation,
    Publish,
}

impl Instruction {
    fn from(value: u8) -> Instruction {
        match value {
            1 => Instruction::List,
            2 => Instruction::EVar,
            3 => Instruction::SVar,
            4 => Instruction::Symbol,
            5 => Instruction::Implication,
            6 => Instruction::Application,
            7 => Instruction::Mu,
            8 => Instruction::Exists,
            9 => Instruction::MetaVar,
            10 => Instruction::ESubst,
            11 => Instruction::SSubst,
            12 => Instruction::Prop1,
            13 => Instruction::Prop2,
            14 => Instruction::Prop3,
            15 => Instruction::Quantifier,
            16 => Instruction::PropagationOr,
            17 => Instruction::PropagationExists,
            18 => Instruction::PreFixpoint,
            19 => Instruction::Existance,
            20 => Instruction::Singleton,
            21 => Instruction::ModusPonens,
            22 => Instruction::Generalization,
            23 => Instruction::Frame,
            24 => Instruction::Substitution,
            25 => Instruction::KnasterTarski,
            26 => Instruction::Instantiate,
            27 => Instruction::Pop,
            28 => Instruction::Save,
            29 => Instruction::Load,
            30 => Instruction::Publish,
            _ => panic!("Bad Instruction!"),
        }
    }
}

/// Terms
/// =====
///
/// Terms define the in-memory representation of matching logic patterns and proofs.
/// However, since we only implement a proof checker in this program we do not need
/// an explicit representation of the entire hilbert proof tree.
/// We only need to store the conclusion of things that are proved so far.
/// We use the `Proved` variant for this.

#[derive(Debug, Eq, PartialEq, Clone)]
pub enum Pattern {
    EVar(u8),
    SVar(u8),
    Symbol(u8),
    Implication {
        left: Rc<Pattern>,
        right: Rc<Pattern>,
    },
    Application {
        left: Rc<Pattern>,
        right: Rc<Pattern>,
    },
    Exists {
        var: u8,
        subpattern: Rc<Pattern>,
    },
    Mu {
        var: u8,
        subpattern: Rc<Pattern>,
    },
    MetaVar {
        id: u8,
        e_fresh: Vec<u8>,
        s_fresh: Vec<u8>,
        positive: Vec<u8>,
        negative: Vec<u8>,
        application_context: Vec<u8>,
    },
    ESubst {
        pattern: Rc<Pattern>,
        evar_id: u8,
        plug: Rc<Pattern>,
    },
    #[allow(dead_code)]
    SSubst {
        pattern: Rc<Pattern>,
        svar_id: u8,
        plug: Rc<Pattern>,
    },
}

impl Pattern {
    fn e_fresh(&self, evar: u8) -> bool {
        match self {
            Pattern::EVar(name) => *name != evar,
            Pattern::SVar(_) => true,
            Pattern::Symbol(_) => true,
            Pattern::Implication { left, right } => left.e_fresh(evar) && right.e_fresh(evar),
            Pattern::Application { left, right } => left.e_fresh(evar) && right.e_fresh(evar),
            Pattern::Exists { var, subpattern } => evar == *var || subpattern.e_fresh(evar),
            Pattern::Mu { subpattern, .. } => subpattern.e_fresh(evar),
            Pattern::MetaVar { e_fresh, .. } => e_fresh.contains(&evar),
            Pattern::ESubst {
                pattern,
                evar_id,
                plug,
            } => {
                // Assume: substitution is well-formed => plug occurs in the result

                if evar == *evar_id {
                    // Freshness depends only on plug, as all the free instances
                    // of the requested variable are being substituted
                    return plug.e_fresh(evar);
                }

                // Freshness depends on both input and plug,
                // as evar != evar_id (note that instances of evar_id
                // in pattern do not influence the result)
                pattern.e_fresh(evar) && plug.e_fresh(evar)
            }
            _ => {
                unimplemented!("e_fresh unimplemented for this case");
            }
        }
    }

    fn s_fresh(&self, svar: u8) -> bool {
        match self {
            Pattern::SVar(name) => *name != svar,
            Pattern::EVar(_) => true,
            Pattern::Symbol(_) => true,
            Pattern::Implication { left, right } => left.s_fresh(svar) && right.s_fresh(svar),
            Pattern::Application { left, right } => left.s_fresh(svar) && right.s_fresh(svar),
            Pattern::Mu { var, subpattern } => svar == *var || subpattern.s_fresh(svar),
            Pattern::Exists { subpattern, .. } => subpattern.s_fresh(svar),
            Pattern::MetaVar { s_fresh, .. } => s_fresh.contains(&svar),
            Pattern::ESubst { pattern, plug, .. } =>
                // Assume: substitution is well-formed => plug occurs in the result

                // We can skip checking svar == evar_id, because different types

                // Freshness depends on both input and plug,
                // as evar_id != svar (note that instances of evar_id
                // in pattern do not influence the result)
                pattern.s_fresh(svar) && plug.s_fresh(svar),
            _ => {
                unimplemented!("e_fresh unimplemented for this case");
            }
        }
    }

    // TODO: Implement positivity checking
    fn positive(&self, _svar: u8) -> bool {
        unimplemented!("Positivity is not implemented yet.")
    }

    #[allow(dead_code)]
    fn well_formed(&self) -> bool {
        match self {
            Pattern::MetaVar { .. } => {
                // TODO: Should basically determin whether metavar is instantiable
                unimplemented!("Well-formedness checking is unimplemented yet for metavars.");
            }
            Pattern::Mu { var, subpattern } => subpattern.positive(*var),
            Pattern::ESubst {
                pattern,
                evar_id,
                plug,
            } => {
                if pattern.e_fresh(*evar_id) {
                    return false;
                }

                pattern.well_formed() && plug.well_formed()
            }
            Pattern::SSubst {
                pattern,
                svar_id,
                plug,
            } => {
                if pattern.s_fresh(*svar_id) {
                    return false;
                }

                pattern.well_formed() && plug.well_formed()
            }
            _ => {
                // Should default to true except for the cases above
                // TODO: Check
                unimplemented!(
                    "Well-formedness checking is unimplemented yet for this kind of pattern."
                );
            }
        }
    }
}

#[derive(Debug, Eq, PartialEq, Clone)]
pub enum Term {
    Pattern(Rc<Pattern>),
    Proved(Rc<Pattern>),
    List(Vec<u8>),
}
#[derive(Debug, Eq, PartialEq)]
pub enum Entry {
    Pattern(Rc<Pattern>),
    Proved(Rc<Pattern>),
}

/// Pattern construction utilities
/// ------------------------------

fn evar(id: u8) -> Rc<Pattern> {
    return Rc::new(Pattern::EVar(id));
}

fn svar(id: u8) -> Rc<Pattern> {
    return Rc::new(Pattern::SVar(id));
}

fn symbol(id: u8) -> Rc<Pattern> {
    return Rc::new(Pattern::Symbol(id));
}

fn exists(var: u8, subpattern: Rc<Pattern>) -> Rc<Pattern> {
    return Rc::new(Pattern::Exists { var, subpattern });
}

// Does not do any well-formedness checks!!!!!
fn mu(var: u8, subpattern: Rc<Pattern>) -> Rc<Pattern> {
    return Rc::new(Pattern::Mu { var, subpattern });
}

fn esubst(pattern: Rc<Pattern>, evar_id: u8, plug: Rc<Pattern>) -> Rc<Pattern> {
    return Rc::new(Pattern::ESubst {
        pattern,
        evar_id,
        plug,
    });
}

fn metavar_unconstrained(var_id: u8) -> Rc<Pattern> {
    return Rc::new(Pattern::MetaVar {
        id: var_id,
        e_fresh: vec![],
        s_fresh: vec![],
        positive: vec![],
        negative: vec![],
        application_context: vec![],
    });
}

fn implies(left: Rc<Pattern>, right: Rc<Pattern>) -> Rc<Pattern> {
    return Rc::new(Pattern::Implication { left, right });
}

fn app(left: Rc<Pattern>, right: Rc<Pattern>) -> Rc<Pattern> {
    return Rc::new(Pattern::Application { left, right });
}

#[cfg(test)]
fn metavar_s_fresh(var_id: u8, fresh: u8, positive: Vec<u8>, negative: Vec<u8>) -> Rc<Pattern> {
    return Rc::new(Pattern::MetaVar {
        id: var_id,
        e_fresh: vec![],
        s_fresh: vec![fresh],
        positive,
        negative,
        application_context: vec![],
    });
}

// Notation
fn bot() -> Rc<Pattern> {
    mu(0, svar(0))
}

fn not(pat: Rc<Pattern>) -> Rc<Pattern> {
    implies(pat, Rc::clone(&bot()))
}

#[allow(dead_code)]
fn forall(evar: u8, pat: Rc<Pattern>) -> Rc<Pattern> {
    not(exists(evar, not(pat)))
}

/// Substitution utilities
/// ----------------------

fn instantiate(p: Rc<Pattern>, vars: &Vec<u8>, plugs: &Vec<Rc<Pattern>>) -> Rc<Pattern> {
    match p.as_ref() {
        Pattern::Implication { left, right } => implies(
            instantiate(Rc::clone(&left), vars, plugs),
            instantiate(Rc::clone(&right), vars, plugs),
        ),
        Pattern::MetaVar {
            id,
            e_fresh,
            s_fresh,
            ..
        } => {
            if let Some(pos) = vars.iter().position(|&x| x == *id) {
                // TODO: Improve performance
                // This introduces 3000 cycles on proof of phi -> phi with empty e_fresh, s_fresh
                for evar in e_fresh {
                    if !plugs[pos].e_fresh(*evar) {
                        panic!(
                            "Instantiation of MetaVar {} breaks a freshness constraint: EVar {}",
                            id, evar
                        );
                    }
                }
                for svar in s_fresh {
                    if !plugs[pos].s_fresh(*svar) {
                        panic!(
                            "Instantiation of MetaVar {} breaks a freshness constraint: SVar {}",
                            id, svar
                        );
                    }
                }

                return Rc::clone(&plugs[pos]);
            }

            p
        }
        _ => unimplemented!("Instantiation failed"),
    }
}

/// Proof checker
/// =============

type Stack = Vec<Term>;
type Claims = Vec<Term>;
type Memory = Vec<Entry>;

/// Stack utilities
/// ---------------

fn pop_stack(stack: &mut Stack) -> Term {
    return stack.pop().expect("Insufficient stack items.");
}

fn pop_stack_list(stack: &mut Stack) -> Vec<u8> {
    match pop_stack(stack) {
        Term::List(l) => return l,
        _ => panic!("Expected list on stack."),
    }
}

fn pop_stack_pattern(stack: &mut Stack) -> Rc<Pattern> {
    match pop_stack(stack) {
        Term::Pattern(p) => return p,
        _ => panic!("Expected pattern on stack."),
    }
}

fn pop_stack_proved(stack: &mut Stack) -> Rc<Pattern> {
    match pop_stack(stack) {
        Term::Proved(p) => return p,
        _ => panic!("Expected proved on stack."),
    }
}

/// Main implementation
/// -------------------

fn execute_instructions<'a>(
    next: &mut impl FnMut() -> Option<u8>,
    stack: &mut Stack,
    memory: &mut Memory,
    claims: &mut Claims,
) {
    // Metavars
    let phi0 = metavar_unconstrained(0);
    let phi1 = metavar_unconstrained(1);
    let phi2 = metavar_unconstrained(2);

    // Axioms
    let prop1 = implies(
        Rc::clone(&phi0),
        implies(Rc::clone(&phi1), Rc::clone(&phi0)),
    );
    let prop2 = implies(
        implies(
            Rc::clone(&phi0),
            implies(Rc::clone(&phi1), Rc::clone(&phi2)),
        ),
        implies(
            implies(Rc::clone(&phi0), Rc::clone(&phi1)),
            implies(Rc::clone(&phi0), Rc::clone(&phi2)),
        ),
    );
    let prop3 = implies(not(not(Rc::clone(&phi0))), Rc::clone(&phi0));
    let quantifier = implies(
        esubst(Rc::clone(&phi0), 0, evar(1)),
        exists(0, Rc::clone(&phi0)),
    );

    while let Some(instr_u32) = next() {
        match Instruction::from(instr_u32) {
            Instruction::List => {
                let len = next().expect("Insufficient parameters for List instruction");
                if len != 0 {
                    panic!("Len was supposed to be zero.")
                }
                let list = vec![];
                stack.push(Term::List(list));
            }
            // TODO: Add an abstraction for pushing these one-argument terms on stack?
            Instruction::EVar => {
                let id = next().expect("Expected id for the EVar to be put on stack");

                stack.push(Term::Pattern(evar(id)));
            }
            Instruction::SVar => {
                let id = next().expect("Expected id for the SVar to be put on stack");

                stack.push(Term::Pattern(svar(id)));
            }
            Instruction::Symbol => {
                let id = next().expect("Expected id for the Symbol to be put on stack");

                stack.push(Term::Pattern(symbol(id)));
            }
            Instruction::Implication => {
                let right = pop_stack_pattern(stack);
                let left = pop_stack_pattern(stack);
                stack.push(Term::Pattern(implies(left, right)))
            }
            Instruction::Application => {
                let right = pop_stack_pattern(stack);
                let left = pop_stack_pattern(stack);
                stack.push(Term::Pattern(app(left, right)))
            }
            Instruction::Exists => {
                let id = next().expect("Expected var_id for the exists binder");
                let subpattern = pop_stack_pattern(stack);
                stack.push(Term::Pattern(exists(id, subpattern)))
            }
            Instruction::MetaVar => {
                let id = next().expect("Insufficient parameters for MetaVar instruction");
                let application_context = pop_stack_list(stack);
                let negative = pop_stack_list(stack);
                let positive = pop_stack_list(stack);
                let s_fresh = pop_stack_list(stack);
                let e_fresh = pop_stack_list(stack);
                stack.push(Term::Pattern(Rc::new(Pattern::MetaVar {
                    id,
                    e_fresh,
                    s_fresh,
                    positive,
                    negative,
                    application_context,
                })));
            }
            Instruction::ESubst => {
                let evar_id = next().expect("Insufficient parameters for ESubst instruction");
                let pattern = pop_stack_pattern(stack);
                let plug = pop_stack_pattern(stack);
                stack.push(Term::Pattern(esubst(pattern, evar_id, plug)));
            }

            Instruction::Prop1 => {
                stack.push(Term::Proved(Rc::clone(&prop1)));
            }
            Instruction::Prop2 => {
                stack.push(Term::Proved(Rc::clone(&prop2)));
            }
            Instruction::Prop3 => {
                stack.push(Term::Proved(Rc::clone(&prop3)));
            }
            Instruction::ModusPonens => match pop_stack_proved(stack).as_ref() {
                Pattern::Implication { left, right } => {
                    if *left.as_ref() != *pop_stack_proved(stack).as_ref() {
                        panic!("Antecedents do not match for modus ponens.")
                    }
                    stack.push(Term::Proved(Rc::clone(&right)))
                }
                _ => {
                    panic!("Expected an implication as a first parameter.")
                }
            },
            Instruction::Quantifier => {
                stack.push(Term::Proved(Rc::clone(&quantifier)));
            }
            Instruction::Generalization => match pop_stack_proved(stack).as_ref() {
                Pattern::Implication { left, right } => {
                    let evar = 0;

                    if !right.e_fresh(evar) {
                        panic!("The binding variable has to be fresh in the conclusion.");
                    }

                    stack.push(Term::Proved(implies(
                        exists(evar, Rc::clone(left)),
                        Rc::clone(right),
                    )));
                }
                _ => {
                    panic!("Expected an implication as a first parameter.")
                }
            },
            Instruction::Instantiate => {
                let n = next().expect("Insufficient parameters for Instantiate instruction");
                let mut ids: Vec<u8> = vec![];
                let mut plugs: Vec<Rc<Pattern>> = vec![];

                let mut i = 0;
                while i < n {
                    ids.push(next().expect("Insufficient parameters for Instantiate instruction"));
                    plugs.push(pop_stack_pattern(stack));
                    i += 1;
                }

                let metaterm = pop_stack(stack);
                match metaterm {
                    Term::Pattern(p) => stack.push(Term::Pattern(instantiate(p, &ids, &plugs))),
                    Term::Proved(p) => stack.push(Term::Proved(instantiate(p, &ids, &plugs))),
                    Term::List(_) => panic!("Cannot Instantiate list."),
                }
            }
            Instruction::Pop => {
                stack.pop();
            }
            Instruction::Save => match stack.last().expect("Save needs an entry on the stack") {
                Term::Pattern(p) => memory.push(Entry::Pattern(p.clone())),
                Term::Proved(p) => memory.push(Entry::Proved(p.clone())),
                Term::List(_) => panic!("Cannot Save lists."),
            },
            Instruction::Load => {
                let index = next().expect("Insufficient parameters for Load instruction");
                match &memory[index as usize] {
                    Entry::Pattern(p) => stack.push(Term::Pattern(p.clone())),
                    Entry::Proved(p) => stack.push(Term::Proved(p.clone())),
                }
            }
            Instruction::Publish => {
                let claim = pop_stack_pattern(claims);
                let theorem = pop_stack_proved(stack);

                if claim != theorem {
                    panic!("This proof does not prove the requested claim");
                }
            }
            _ => {
                unimplemented!("Instruction: {}", instr_u32)
            }
        }
    }
}

pub fn verify<'a>(
    proof_next_byte: &mut impl FnMut() -> Option<u8>,
    claims_next_byte: &mut impl FnMut() -> Option<u8>,
) -> (Stack, Memory, Claims) {
    let mut claim_stack = vec![];
    let mut claim_memory = vec![];
    execute_instructions(
        claims_next_byte,
        &mut claim_stack,
        &mut claim_memory,
        &mut vec![],
    );

    let mut proof_stack = vec![];
    let mut proof_memory = vec![];
    execute_instructions(
        proof_next_byte,
        &mut proof_stack,
        &mut proof_memory,
        &mut claim_stack,
    );
    return (proof_stack, proof_memory, claim_stack);
}

/// Testing
/// =======

#[ignore]
#[test]
fn test_negative_disjoint() {
    let phi0_s_fresh_0 = metavar_s_fresh(0, 0, vec![0], vec![]);
    assert!(!phi0_s_fresh_0.well_formed());
}

#[ignore]
#[test]
fn test_positive_disjoint() {
    let phi0_s_fresh_0 = metavar_s_fresh(0, 0, vec![], vec![0]);
    assert!(!phi0_s_fresh_0.well_formed());
}

#[ignore]
#[test]
fn test_wellformedness_fresh() {
    let phi0_s_fresh_0 = metavar_s_fresh(0, 0, vec![0], vec![0]);
    assert!(phi0_s_fresh_0.well_formed());
}

#[ignore]
#[test]
#[should_panic]
fn test_instantiate_fresh() {
    let svar_0 = svar(0);
    let phi0_s_fresh_0 = metavar_s_fresh(0, 0, vec![0], vec![0]);
    _ = instantiate(phi0_s_fresh_0, 0, svar_0);
}

#[test]
fn test_efresh() {
    let evar = evar(1);
    let left = Rc::new(Pattern::Exists {
        var: 1,
        subpattern: evar.clone(),
    });
    assert!(left.e_fresh(1));

    let right = Rc::new(Pattern::Exists {
        var: 2,
        subpattern: evar,
    });
    assert!(!right.e_fresh(1));

    let implication = implies(Rc::clone(&left), right);
    assert!(!implication.e_fresh(1));

    let mvar = metavar_s_fresh(1, 2, vec![2], vec![2]);
    let metaapplication = Pattern::Application { left, right: mvar };
    assert!(!metaapplication.e_fresh(2));
}

#[test]
fn test_sfresh() {
    let svar = svar(1);
    let left = Rc::new(Pattern::Mu {
        var: 1,
        subpattern: svar.clone(),
    });
    assert!(left.s_fresh(1));

    let right = Rc::new(Pattern::Mu {
        var: 2,
        subpattern: svar,
    });
    assert!(!right.s_fresh(1));

    let implication = implies(Rc::clone(&left), right);
    assert!(!implication.s_fresh(1));

    let mvar = metavar_s_fresh(1, 2, vec![2], vec![2]);
    let metaapplication = Pattern::Application {
        left: Rc::clone(&left),
        right: Rc::clone(&mvar),
    };
    assert!(!metaapplication.s_fresh(1));

    let metaapplication2 = Pattern::Application { left, right: mvar };
    assert!(metaapplication2.s_fresh(2));
}

#[test]
fn test_construct_phi_implies_phi() {
    #[rustfmt::skip]
    let proof : Vec<u8> = vec![
        Instruction::List as u8, 0,     // E Fresh
        Instruction::List as u8, 0,     // S Fresh
        Instruction::List as u8, 0,     // Positive
        Instruction::List as u8, 0,     // Negative
        Instruction::List as u8, 0,     // Context
        Instruction::MetaVar as u8, 0,  // Stack: Phi
        Instruction::Save as u8,        // @ 0
        Instruction::Load as u8, 0,     // Phi ; Phi
        Instruction::Implication as u8, // Phi -> Phi
    ];
    let mut iterator = proof.iter();
    let next = &mut (|| iterator.next().cloned());
    let (stack, _journal, _memory) = verify(next, &mut (|| None));
    let phi0 = metavar_unconstrained(0);
    assert_eq!(
        stack,
        vec![Term::Pattern(Rc::new(Pattern::Implication {
            left: phi0.clone(),
            right: phi0.clone()
        }))]
    );
}

#[test]
fn test_phi_implies_phi_impl() {
    #[rustfmt::skip]
    let proof : Vec<u8> = vec![
        Instruction::Prop1 as u8,              // (p1: phi0 -> (phi1 -> phi0))

        Instruction::List as u8, 0,
        Instruction::List as u8, 0,
        Instruction::List as u8, 0,
        Instruction::List as u8, 0,
        Instruction::List as u8, 0,
        Instruction::MetaVar as u8, 0,         // Stack: p1 ; phi0
        Instruction::Save as u8,               // phi0 save at 0

        Instruction::Instantiate as u8, 1, 1,     // Stack: (p2: phi0 -> (phi0 -> phi0))

        Instruction::Prop1 as u8,              // Stack: p2 ; p1
        Instruction::Load as u8, 0,            // Stack: p2 ; p1 ; phi0
        Instruction::Load as u8, 0,            // Stack: p2 ; p1 ; phi0 ; phi0
        Instruction::Implication as u8,        // Stack: p2 ; p1 ; phi1; phi0 -> phi0
        Instruction::Save as u8,               // phi0 -> phi0 save at 1

        Instruction::Instantiate as u8, 1, 1,     // Stack: p2 ; (p3: phi0 -> ((phi0 -> phi0) -> phi0))

        Instruction::Prop2 as u8,              // Stack: p2 ; p3; (p4: (phi0 -> (phi1 -> phi2)) -> ((phi0 -> phi1) -> (phi0 -> phi2))
        Instruction::Load as u8, 1,
        Instruction::Instantiate as u8, 1, 1,     // Stack: p2 ; p3; (p4: (phi0 -> ((phi0 -> phi0) -> phi2)) -> (p2 -> (phi0 -> phi2))

        Instruction::Load as u8, 0,
        Instruction::Instantiate as u8, 1, 2,     // Stack: p2 ; p3; (p4: p3 -> (p2 -> (phi0 -> phi0))

        Instruction::ModusPonens as u8,        // Stack: p2 ; (p2 -> (phi0 -> phi0))
        Instruction::ModusPonens as u8,        // Stack: phi0 -> phi0
    ];
    let mut iterator = proof.iter();
    let next = &mut (|| iterator.next().cloned());
    let (stack, _journal, _memory) = verify(next, &mut (|| None));
    let phi0 = metavar_unconstrained(0);
    assert_eq!(
        stack,
        vec![Term::Proved(Rc::new(Pattern::Implication {
            left: Rc::clone(&phi0),
            right: Rc::clone(&phi0)
        }))]
    )
}

// TODO: Actually pass just phi0 in memory
#[ignore]
#[test]
fn test_universal_quantification() {
    let phi0 = metavar_unconstrained(0);

    #[rustfmt::skip]
    let proof : Vec<u8> = vec![
        Instruction::Load as u8, 0,                   // (p1: not(phi0) -> bot)
        Instruction::Generalization as u8             // (p2: exists not(phi0) -> bot)
    ];
    #[rustfmt::skip]
    let _memory: Memory = vec![
        Entry::Proved(implies(not(Rc::clone(&phi0)), bot()))
    ];

    let mut iterator = proof.iter();
    let next = &mut (|| iterator.next().cloned());
    let (stack, _journal, _memory2) = verify(next, &mut (|| None));

    assert_eq!(stack, vec![Term::Proved(forall(0, Rc::clone(&phi0)))])
}
