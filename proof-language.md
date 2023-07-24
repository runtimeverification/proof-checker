---
geometry: margin=2cm
---

\newcommand{\limplies}{\to}
\renewcommand{\phi}{\varphi}


Matching logic proof format
===========================

This is a proposed matching logic proof format.

## Relation to Metamath

Note that this language heavily based on the metamath format for compressed proofs.
Besides being a binary rather than ASCII encoding, there are two major changes.

1.  We use the same mechanism for constructing terms and proofs, allowing better
    compression.
2.  We allow emmitting multiple proofs from the same representation. This allows
    us to represent lemmas and compression uniformly.
    That is, we can store the entire contents of a single metamath file in this format,
    rather than just the proof of a single lemma.

## Relation to postfix notation/RPN

The format may be viewed as a generalization
of postfix notation (incidentally also called Lukaseiwicz notation),
for an expression computing the conclusion of a proof.

We also allow marking subexpressions (i.e. either proofs or patterns) for reuse. This
allows us to represent lemmas, and compactly representing configurations and notation.

(This needs input from ZK folk.) Finally, we allow marking constructed proofs
as public. This serves two purposes. First, it allows us to publish lemmas
that may be reused in other proofs. Second, it allows us to publish the main
result proved by the proof.


## As a stack machine

It may also be viewed language interpreted using a stack machine.
This stack machines constructs terms---either patterns or proofs. We treat
patterns and proofs uniformly---at an abstract level, they are both terms we
must construct, with particular well-formedness criteria. It is intended for the
most part, that **the verifier only needs to keep proved conclusions in
memory**.


## Goals:

-   No upfront parsing cost.
-   Easily verifiable using ZK.
-   Low memory usage.
-   Composability.


## Non-goals:

-   Parallization: I have not been thinking explicitly about parallel verification of this format,
    because I expect parallization to happen by composing units of this format into larger proofs.
    Even so I think with some additional metadata, we could make
    this format parallizable.

-   Human readability: We aim to be a simple binary format. To become human
    readable, we expect the user to run a secondary program to pretty-print the
    proof. Note that symbols, lemmas, and notation do not have names.


Terms
=====

As mentioned previously, we may view this format as a language for constructing
terms that meet particular well-formedness criteria. Let us first enumerate
those terms, in a python-esque pseudocode.

`Term`s are of two types, `Pattern`, and `Proof`.
Every `Term` has a well-formedness check.
Every `Proof` has a conclusion.

```python
abstract class Term:
    abstract def well_formed:
        ...

abstract class Pattern(Term):
    def well_formed():
        # Fails if any two MetaVars with the same id has
        # different meta-requirements
        # MetaVars are introduced later.
    ...

abstract class Proof(Term):
    abstract def conclusion:
        ...
```

`Pattern`s
----------

There are two classes of `Pattern`,
the expected concrete constructors for matching logic patterns,
and a representation for various "meta" patterns.

### Standard patterns

```python
class Symbol(Pattern):
    name: u32

class SVar(Pattern):
    name: u32

class EVar(Pattern):
    name: u32

class Implication(Pattern):
    left: Pattern
    right: Pattern

class Application(Pattern):
    left: Pattern
    right: Pattern

class Exists(Pattern):
    var: EVar
    subpattern : Pattern

class Mu(Pattern):
    var: SVar
    subpattern : Pattern

    def well_formed():
        return super.well_formed()
           and subpattern.var_occurs_positively(var)
```

### Meta-patterns

Meta-patterns allow us to represent axiom- and theorem-schemas through the use
of metavariables:

```python
class MetaVar(Pattern):
    name: u32

    # Meta-requirements that must be satisfied by any instantiation.
    e_fresh: list[u32]             # Element variables that must not occur in an instatiation
    s_fresh: list[u32]             # Set variables that must not occur in an instatiation
    positive: list[u32]            # Set variables that must only occur positively in an instatiation
    negative: list[u32]            # Set variables that must only occur negatively in an instatiation
    application_context: list[u32] # Element variables that must only occur as a hole variable in an application context.
```

Each `MetaVar` has a list of requirements that must be met by any instantiation.
These may also be used by the well-formedness checks for `Proof`s.

We also need to represent substitutions applied to `MetaVar`s.

```python
class ESubst(Pattern):
    pattern: MetaVar
    var: EVar
    plug: Pattern

class SSubst(Pattern):
    pattern: MetaVar
    var: SVar
    plug: Pattern
```


`Proof`s
--------

### Axiom Schemas

Axiom schemas are `Proof`s that do not need any input arguments.
They may use `MetaVar`s to represent their schematic nature.

```python
class Lukaseiwicz(Proof):
    def conclusion():
        phi1 = MetaVar('phi1')
        return Implication(Implication(Implication(MetaVar(phi1) , ...)...)...)

class Quantifier(Proof):
    def conclusion():
        x = EVar('#x')
        y = EVar('#y')
        phi = MetaVar('phi', fresh=[y])
        return Implication(ESubst(phi, x, y), Exists(x, phi))

class PropagationOr(Proof):
    def conclusion():
        hole = EVar('#hole')
        C = MetaVar(application_context=(EVar('#hole'),))
        phi1 = MetaVar('#phi1')
        phi2 = MetaVar('#phi2')
        return Implication(ESubst(C, or(phi1, phi2), hole), or(ESubst(C, phi1, hole), ESubst(C, phi2, hole)))

...
```


### Meta Variable Instantiation

Using a rule of meta inference, we may instantiate metatheorems.
This allows us to instantiate axiom and theorem schemas, such as
$\phi \limplies \phi$.


```python
class InstantiateSchema(Proof):
    subproof : Proof
    metavar_id: u32
    instantiation: Pattern

    def well_formed():
        # Fails if the instantiation does not meet the
        # disjoint/positive/freshness/application ctx
        # criterea of the metavar.

    def conclusion():
        return subproof.meta_substitute(metavar, instantiation)
```

TODO: Could we just merge this with `InstantiateSchema`?
We may also use metavariables to represent notation.

```python
class InstantiateNotation(Pattern):
    notation: Pattern
    metavar_id: u32
    instantiation: Pattern

    def well_formed():
        # Fails if the instantiation does not meet the
        # disjoint/positive/freshness/application ctx
        # criterea of the metavar.

    def conclusion():
        return notation.meta_substitute(metavar, instantiation)
```


### Ordinary inference

```python
class ModusPonens(Proof):
    premise_left: Implication
    premise_right: Pattern

    def conclusion():
        return premise_left.right

    def well_formed():
        assert premise_right == premise_left.left

class Generalization(Proof):
    premise: Implication

    def phi1():
        premise.left
    def phi2():
        premise.right

    def conclusion():
        return Implication(ESubst(MetaVar(phi), EVar(x), EVar(y)), Exists(EVar(x), MetaVar(phi)))

    def well_formed():
        assert EVar(x) is fresh in phi1()
...
```

Verification
============

The verifier operates in three phases---the `gamma` phase, the `claim` phase, and the `proof` phase.
The `gamma` phase sets up the axioms that may be used in the proof.
The `claim` phase sets up claims, or theorems expected to be proved.
These two phases consume input from a "public" file, in ZK terminology.
The third phase, `proof`, proves each of these claims using the axioms.
The input to this phase is "private" in ZK terminology, allowing up us to roll-up the proof.
The semantics of instructions in each of these phases is identical, except
for the publish instruction. We will expand on this later.

The verifier's state consists of:

*   a *stack* of terms (i.e. lists of ids, patterns and proved conclusions).
*   a *memory* consisting of previously constructed patterns and proven conclusions that may be reused for later proofs.
*   only during the phase `gamma`, a write-only list of axioms.
    At the beginning of the `proof` phase this list of axioms will be used to pre-populate the memory.
*   only during the phases `claim` and `proof`: a queue of claims to be proved.

The verifier's input consists of three files, one for each phase.
These files are at a logical level. Depending on the circumstances
the implementation may choose to represent them as three distinct OS files,
or a single input stream separated by the `EOF` instruction.
In the case of Risc0, we will likely combine the first two files, since they are public
and keep the third separate, since it is private.

Between phases, the stack and memory are cleared.
Before the the start of the second phase,
the list of axioms populated in the first phase is used to initialize the memory.

> TODO: We need to think about this.
> I'd like notation to be shared between the phases,
> but don't want arbitary intermediate terms saved to the memory to be shared.
> Should we have an additional instruction for publishing notation?

Instructions and semantics
==========================

Each of these instructions checks that the constructed `Term` is well-formed before pushing onto the stack.
Otherwise, execution aborts, and verification fails.

### Supporting

`List n:u32 [u32]*n`
:   Consume a length $n$, and $n$ items from the input.
    Push a list containing those `u32`s to the stack.


### Variables and Symbols:

`EVar <u32>`
:   Push an `EVar` onto the stack.

`SVar <u32>`
:   Push a `SVar` onto the stack.

`Symbol <u32>`
:   Push a `Symbol` onto the stack.

`MetaVar <u32>`
:   Consume the first five entries from the stack (corresponding to the
    meta-requirements), and push an `MetaVar` onto the stack.


`Implication`/`Application`/`Exists`/`Mu`
:   Consume the two patterns from the stack,
    and push an implication/application/exists/mu to the stack
    with appropriate arguments, performing well formedness checks as needed.

### Axiom Schemas

`Lukaseiwicz`/`Quantifier`/`PropagationOr`/`PropagationExists`/`PreFixpoint`/`Existance`/`Singleton`
:   Push proof term corresponding to axiom schema onto the stack.

### Meta inference

`Instantiate <metavar_id:u32>`
:   Consume a `Proof` and `Pattern` off the stack, and push the instantiated proof term to the stack,
    checking wellformedness as needed.

### Inference rules

`ModusPonens`/`Generalization`/`Frame`/`Substitution`/`KnasterTarski`
:   Consume one or two `Proof` terms off the stack and push the new proof term.

### Memory manipulation:

`Save`
:   Store the top of the stack to the lowest unused index in memory.

`Load i:u32`
:   Push the `Term` at index $i$ to the top of the stack.

`Delete i:u32`
:   Remove the `Term` at index $i$ from memory. This is not strictly needed, but
    will allow the verifier to use less memory. The memory slot is not
    considered for reuse by the `Save` instruction.


### Journal manipulation.

`Publish`
:   * During the `gamma` phase, consume a pattern from the stack and push it to the list of axioms.
    * During the `claim` phase consume a pattern from the stack and push it to the queue of claims.
    * During the `proof` phase consume a proof from the stack
      and a claim from the queue of claims and assert that they are equal.


### Stack manipulation.

`Pop`
:   Consume the top of the stack.

### Technical

`EOF`
:   End the current phase.

