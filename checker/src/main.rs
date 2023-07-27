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
    InstantiateNotation, InstantiateSchema,
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
            26 => Instruction::InstantiateNotation,
            27 => Instruction::InstantiateSchema,
            28 => Instruction::Pop,
            29 => Instruction::Save,
            30 => Instruction::Load,
            31 => Instruction::Publish,
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
    #[allow(dead_code)]
    EVar(u8),
    #[allow(dead_code)]
    SVar(u8),
    #[allow(dead_code)]
    Symbol(u8),
    Implication {
        left: Rc<Pattern>,
        right: Rc<Pattern>,
    },
    #[allow(dead_code)]
    Application {
        left: Rc<Pattern>,
        right: Rc<Pattern>,
    },
    #[allow(dead_code)]
    Exists { var: u8, subpattern: Rc<Pattern> },
    #[allow(dead_code)]
    Mu { var: u8, subpattern: Rc<Pattern> },

    MetaVar {
        id: u8,
        e_fresh: Vec<u8>,
        s_fresh: Vec<u8>,
        positive: Vec<u8>,
        negative: Vec<u8>,
        application_context: Vec<u8>,
    },
}

impl Pattern {
    #[allow(dead_code)]
    fn well_formed(&self) -> bool {
        unimplemented!("Well-formedness checking is unimplemented yet");
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

#[cfg(test)]
fn svar(id: u8) -> Rc<Pattern> {
    return Rc::new(Pattern::SVar(id));
}

fn implies(left: Rc<Pattern>, right: Rc<Pattern>) -> Rc<Pattern> {
    return Rc::new(Pattern::Implication { left, right });
}

/// Substitution utilities
/// ----------------------

fn instantiate(p: Rc<Pattern>, var_id: u8, plug: Rc<Pattern>) -> Rc<Pattern> {
    match p.as_ref() {
        Pattern::Implication { left, right } => implies(
            instantiate(Rc::clone(&left), var_id, Rc::clone(&plug)),
            instantiate(Rc::clone(&right), var_id, plug),
        ),
        Pattern::MetaVar { id, .. } => {
            if *id == var_id {
                plug
            } else {
                p
            }
        }
        _ => unimplemented!("Instantiation failed"),
    }
}

/// Proof checker
/// =============

type Stack = Vec<Term>;
type Journal = Vec<Entry>;
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
    _journal: &mut Journal,
) {
    // Metavars
    let phi0 = metavar_unconstrained(0);
    let phi1 = metavar_unconstrained(1);
    let phi2 = metavar_unconstrained(2);

    // Axioms
    let prop1 = implies(Rc::clone(&phi0), implies(Rc::clone(&phi1), Rc::clone(&phi0)));
    let prop2 = implies(
        implies(Rc::clone(&phi0), implies(Rc::clone(&phi1), Rc::clone(&phi2))),
        implies(implies(Rc::clone(&phi0), Rc::clone(&phi1)), implies(Rc::clone(&phi0), Rc::clone(&phi2))),
    );

    while let Some(instr_u32) = next() {
        match Instruction::from(instr_u32) {
            Instruction::List => {
                let len = next()
                    .expect("Insufficient parameters for List instruction");
                if len != 0 {
                    panic!("Len was supposed to be zero.")
                }
                let list = vec![];
                stack.push(Term::List(list));
            }
            Instruction::Implication => {
                let right = pop_stack_pattern(stack);
                let left = pop_stack_pattern(stack);
                stack.push(Term::Pattern(implies(left, right)))
            }
            Instruction::MetaVar => {
                let id = next()
                    .expect("Insufficient parameters for MetaVar instruction");
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

            Instruction::Prop1 => {
                stack.push(Term::Proved(Rc::clone(&prop1)));
            }
            Instruction::Prop2 => {
                stack.push(Term::Proved(Rc::clone(&prop2)));
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
            Instruction::InstantiateSchema => {
                let plug = pop_stack_pattern(stack);
                let metavar = pop_stack_pattern(stack);
                match *metavar {
                    Pattern::MetaVar { id, .. } => {
                        let metatheorem = pop_stack_proved(stack);
                        stack.push(Term::Proved(instantiate(metatheorem, id, plug)));
                    }
                    _ => panic!("Expected a metavariable"),
                }
            }

            Instruction::Save => match stack.last().expect("Save needs an entry on the stack") {
                Term::Pattern(p) => memory.push(Entry::Pattern(p.clone())),
                Term::Proved(p) => memory.push(Entry::Proved(p.clone())),
                Term::List(_) => panic!("Cannot Save lists."),
            },
            Instruction::Load => {
                let index = next()
                    .expect("Insufficient parameters for Load instruction");
                match &memory[index as usize] {
                    Entry::Pattern(p) => stack.push(Term::Pattern(p.clone())),
                    Entry::Proved(p) => stack.push(Term::Proved(p.clone())),
                }
            },
            _ => {
                unimplemented!("Instruction: {}", instr_u32)
            }
        }
    }
}

pub fn verify<'a>(next: &mut impl FnMut() -> Option<u8>) -> (Stack, Journal, Memory) {
    let mut stack = vec![];
    let mut journal = vec![];
    let mut memory = vec![];
    execute_instructions(next, &mut stack, &mut journal, &mut memory);
    return (stack, journal, memory);
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
fn test_construct_phi_implies_phi() {
    #[rustfmt::skip]
    let proof : Vec<u8> = vec![
        Instruction::List as u8, 0, // E Fresh
        Instruction::List as u8, 0, // S Fresh
        Instruction::List as u8, 0, // Positive
        Instruction::List as u8, 0, // Negative
        Instruction::List as u8, 0, // Context
        Instruction::MetaVar as u8, 0, // Stack: Phi
        Instruction::Save as u8,    // @ 0
        Instruction::Load as u8, 0, // Phi ; Phi
        Instruction::Implication as u8, // Phi -> Phi
    ];
    let mut iterator = proof.iter();
    let next = &mut (|| iterator.next().cloned());
    let (stack, _journal, _memory) = verify(next);
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
        Instruction::Prop1 as u8,               // (p1: phi0 -> (phi1 -> phi0))

        Instruction::List as u8, 0,
        Instruction::List as u8, 0,
        Instruction::List as u8, 0,
        Instruction::List as u8, 0,
        Instruction::List as u8, 0,
        Instruction::MetaVar as u8, 1,          // Stack: p1 ; phi1
        Instruction::Save as u8,                // phi1 save at 0

        Instruction::List as u8, 0,
        Instruction::List as u8, 0,
        Instruction::List as u8, 0,
        Instruction::List as u8, 0,
        Instruction::List as u8, 0,
        Instruction::MetaVar as u8, 0,          // Stack: p1 ; phi1 ; phi0
        Instruction::Save as u8,                // phi0 save at 1

        Instruction::InstantiateSchema as u8,   // Stack: (p2: phi0 -> (phi0 -> phi0))

        Instruction::Prop1 as u8,               // Stack: p2 ; p1
        Instruction::Load as u8, 0,             // Stack: p2 ; p1 ; phi1
        Instruction::Load as u8, 1,             // Stack: p2 ; p1 ; phi0
        Instruction::Load as u8, 1,             // Stack: p2 ; p1 ; phi0 ; phi0
        Instruction::Implication as u8,         // Stack: p2 ; p1 ; phi1; phi0 -> phi0

        Instruction::Save as u8,                // phi0 -> phi0 save at 3

        Instruction::InstantiateSchema as u8,   // Stack: p2 ; (p3: phi0 -> (phi0 -> phi0) -> phi0)

        Instruction::Prop2 as u8,               // Stack: p2 ; p3; (p4: (phi0 -> (phi1 -> phi2)) -> ((phi0 -> phi1) -> (phi0 -> phi2))
        Instruction::Load as u8, 0,
        Instruction::Load as u8, 2,
        Instruction::InstantiateSchema as u8,

        Instruction::List as u8, 0,
        Instruction::List as u8, 0,
        Instruction::List as u8, 0,
        Instruction::List as u8, 0,
        Instruction::List as u8, 0,
        Instruction::MetaVar as u8, 2,
        Instruction::Load as u8, 1,
        Instruction::InstantiateSchema as u8,

        Instruction::ModusPonens as u8,
        Instruction::ModusPonens as u8,         // Stack: phi0 -> phi0
    ];
    let mut iterator = proof.iter();
    let next = &mut (|| iterator.next().cloned());
    let (stack, _journal, _memory) = verify(next);
    let phi0 = metavar_unconstrained(0);
    assert_eq!(stack, vec![Term::Proved(Rc::new(Pattern::Implication{
        left: Rc::clone(&phi0),
        right: Rc::clone(&phi0)
    }))])
}
