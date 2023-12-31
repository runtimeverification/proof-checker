---
geometry: margin=2cm
---

\newcommand{\limplies}{\to}
\renewcommand{\phi}{\varphi}
\newcommand{\union}{\cup}

Motivation
==========

K's behaviour has its mathematical foundation matching logic. Each of its
constructs may be reduced to simpler and more fundamental concepts in matching
logic. Each of the K tools such as `krun`, `kprove`, etc. can, *in theory*,
explain themselves in terms of matching logic. Our goal is to change that theory
to practice. We want to instrument each of these tools with enough information
to generate formal matching logic proofs.

There are two things we need to make this work. First, we need a *proof
checker*---a program that takes as input a matching logic proof and checks
that it is correct. We need this program to be small and simple, so we can
easily verify it (at first by manual inspection, and eventually through formal
verification). It also needs to be fast and efficient to be practical, since
proofs can be hundreds of thousands of steps long.

The second is a proof generator. It will take the instrumentation generated by
the backends, and produce a matching logic proof. In [previous work], we wrote
such a generator for a logic-agnostic proof checker called Metamath.

[previous work]: https://xchen.page/assets/pdf/LCT+23-paper.pdf "Generating Proof Certificates for a Language-Agnostic Deductive Program Verifier"

Unfortunately, we have realized that the Metamath does not meet our needs. Since
it is not matching logic specific, it is very verbose. It is intended to be
somewhat human readable (though it is debatable whether it achieves this) at the
cost of efficiency. It's also a pretty complex language. This has made matching
logic proofs using it massive (we've seen some that are gigabytes), and
impractical.

This has motivated us to define our own compact binary format,
tailored to matching logic. Its essence is a giant postfix/reverse polish
notation representation of a matching logic proof as a DAG. We think that this
will allow us to greatly speed up proof checking.


FAQ
===

>   Is the huge size of the proofs only due to using metamath?
>
>   My understanding was that it's also due to the (too) small axiomatization
>   used for ML which requires some results (e.g., such that one would prove
>   generically by induction of the size of the proof term) to be instead
>   reproved in each concrete instance they are used.
>
>   I know that at some point Brandon implemented a prover directly on top
>   of the haskell backend, and managed to produce a proof of ~2GB showing
>   something along the lines of 1 + 1 = 2

I'm not sure what Brandon's formalization looked like exactly. It's possible
that both the Metamath and our new proposed format are at slightly higher level
than Brandon's.

While we're trying to keep things as low level as we can while still being
practical---so we allow things like metavariables. Meta-variables let us avoid
re-proving theorems for each concrete instance---we can instantiate the
meta-variables with concrete patterns, and reuse the proofs.

In my experience with proof generation in Metamath and Metamath
Zero (another checker), a huge part of proof size is carefully choosing the
appropriate lemmas.

With metamath this is even more tricky, because it is expensive even to restate
a lemma when pattern/configuration sizes are big. The new format addresses
this by allowing sharing of common subpatterns by essentially treating proofs
and patterns uniformly---we may share subpatterns the same way lemmas allow us
to share subproofs.

The second problem we had with metamath is that a majority
of the proof become proving the well-formedness of patterns over and over again.
Since there is a simple decision procedure to check this, there are huge space
savings from directly implementing this in the checker.


> ... I thought that the advantage of using Metamath would be that it would be easier to trust.

The Metamath checker itself is easy to trust because it has a large community behind it, that has been extensively vetted it.
But, besides the checker, we must also trust the specifications and theories written in Metamath.
It is established that Metamath makes it easy to write incorrect specifications.

1.  Notation is typically defined as trusted axioms in Metamath.
    Incorrectly or unsound notation would allow us to prove all sorts of things,
    when we were only expecting a conservative extension.

2.  Worse, the syntax of the logic is defined as axioms. This makes it easy to
    define an ambiguous grammar, especially in the presence of notation. Note
    that metamath doesn't have a native concept of terms, but works over strings
    of tokens. So it is even possible for unbalanced parenthesis to be a "formula".

[set.mm] and other Metamath repositories dealt with this with external tools
to make sure notation and grammar are well-formed. But, these tools are now part
of our trust base?
We will need all sorts of well-formedness checkers for metamath+ML specifications
people write.

[set.mm]: https://github.com/metamath/set.mm/blob/develop/set.mm

> Why is proof generation done in Python, while the proof checker in Rust?

The proof generation code will need to integrate
with the K pyk library. Besides, we care more about ease of writing proofs, than
efficiency or verifiability as in the proof-checker.

These goals directly contradict the goals of the checker since it needs to be
streamlined, both for efficiency and ease of verification---we even avoid basic
debugging and pretty printing to save on complexity. So, even if we wrote
the proof generation code in rust, it would make sense to not reuse the
checkers code.


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
of postfix notation (incidentally also called Lukasiewicz notation),
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
    because I expect parallelization to happen by composing units of this format into larger proofs.
    Even so I think with some additional metadata, we could make
    this format parallelizable.

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
        # returns true if a pattern of given type is well-formed
    ...

    def e_fresh(evar):
        # returns true iff evar is not a free element variable in this pattern
    ...

    def s_fresh(svar):
        # returns true iff svar is not a free set variable in this pattern
    ...

    def positive(svar):
        # returns true iff all free occurrences of svar in this pattern are positive
    ...

    def negative(svar):
        # returns true iff all free occurences of svar in this pattern are negative
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
    name: u8

    def e_fresh(evar):
        return True

    def s_fresh(svar):
        return True

    def positive(svar):
        return True

    def negative(svar):
        return True

    def well_formed():
        return True

class SVar(Pattern):
    name: u8

    def e_fresh(evar):
        return True

    def s_fresh(svar):
        return svar != name

    def positive(svar):
        return True

    def negative(svar):
        return svar != name

    def well_formed():
        return True

class EVar(Pattern):
    name: u8

    def e_fresh(evar):
        return evar != name

    def s_fresh(svar):
        return True

    def positive(svar):
        return True

    def negative(svar):
        return True

    def well_formed():
        return True

class Implies(Pattern):
    left: Pattern
    right: Pattern

    def e_fresh(evar):
        return left.e_fresh(evar) and right.e_fresh(evar)

    def s_fresh(svar):
        return left.s_fresh(svar) and right.s_fresh(svar)

    def positive(svar):
        return left.negative(svar) and right.positive(svar)

    def negative(svar):
        return left.positive(svar) and right.negative(svar)

    def well_formed():
        return left.well_formed()
           and right.well_formed()

class App(Pattern):
    left: Pattern
    right: Pattern

    def e_fresh(evar):
        return left.e_fresh(evar) and right.e_fresh(evar)

    def s_fresh(svar):
        return left.s_fresh(svar) and right.s_fresh(svar)

    def positive(svar):
        return left.positive(svar) and right.positive(svar)

    def negative(svar):
        return left.negative(svar) and right.negative(svar)

    def well_formed():
        return left.well_formed()
           and right.well_formed()

class Exists(Pattern):
    var: u8
    subpattern: Pattern

    def e_fresh(evar):
        return evar == var or subpattern.e_fresh(evar)

    def s_fresh(svar):
        return subpattern.s_fresh(svar)

    def positive(svar):
        return subpattern.positive(svar)

    def negative(svar):
        return subpattern.negative(svar)

    def well_formed():
        return subpattern.well_formed()

class Mu(Pattern):
    var: u8
    subpattern: Pattern

    def e_fresh(evar):
        return subpattern.e_fresh(evar)

    def s_fresh(svar):
        return var == svar or subpattern.s_fresh(svar)

    def positive(svar):
        return svar == var or subpattern.positive(svar)

    def negative(svar):
        return svar == var or subpattern.negative(svar)

    def well_formed():
        return subpattern.well_formed()
           and subpattern.positive(var)
```

### Meta-patterns

Meta-patterns allow us to represent axiom- and theorem-schemas through the use
of metavariables.
Each `MetaVar` has several sets of constraints that must be met by any instantiation.
These may also be used by the well-formedness checks for `Proof`s.
Since we only know constraints of a meta-pattern, constraint checking is best-effort.
This means we want to reject anything that we can't prove to be satisfy the constraints.
For well-formedness, we use the same meta-reasoning as the one used by the MM formalization
(denoted with the comments):

```python
class MetaVar(Pattern):
    name: u8

    # Meta-requirements that must be satisfied by any instantiation.
    e_fresh: set[u8]             # Element variables that must not occur free in an instatiation
    s_fresh: set[u8]             # Set variables that must not occur free in an instatiation
    positive: set[u8]            # Set variables that must only occur positively in an instatiation
    negative: set[u8]            # Set variables that must only occur negatively in an instatiation
    app_ctx_holes: set[u8] # Element variables that must occur as a hole variable in an application context.

    def e_fresh(evar):
        return evar in e_fresh

    def s_fresh(svar):
        return svar in s_fresh

    def positive(svar):
        return svar in positive

    def negative(svar):
        return svar in negative

    # Should check whether the metavar is instantiable, as uninstantiable metavars might lead to issues
    # (see https://github.com/runtimeverification/proof-checker/issues/8)
    def well_formed():
        return app_ctx_holes.disjoint(e_fresh)
```

We also need to represent substitutions applied to `MetaVar`s.

```python
class ESubst(Pattern):
    pattern: MetaVar | SSubst | ESubst
    var: u8
    plug: Pattern

    def well_formed():
        # We do not allow redundant substitutions, since it reduces need the meta-inference for freshness etc.
        if var == plug:           return False  # This is the identity substitution, and so is redundant.
        if pattern.e_fresh(var):  return False  # The variable does not occur, so this is redundant
        # Now we know at least one element variable will be substituted, so we need to check
        # well-formedness of both pattern and plug
        return pattern.well_formed() and plug.well_formed()

    def e_fresh(evar):
        # We can skip the case pattern.e_fresh(var) == true, as
        # such a substitution is malformed by assumption

        if evar == var:
            # This means there are free instances of evar == var and all of them
            # are being substituted for plug, so its freshness depends on plug
            return plug.e_fresh(evar)       # fresh-in-subst

        # There are free instances of var being substituted and svar != var, so
        # we need to check for freshness of svar in both the original pattern
        # and the plugged pattern.
        # Note that it's fine that the original pattern still contains
        # free instances of var => we know that those won't affect
        # the result as svar != var
        return pattern.e_fresh(evar) and plug.e_fresh(evar) # fresh-after-subst

    def s_fresh(svar):
        # We can skip the case pattern.e_fresh(var) == true, as
        # such a substitution is malformed by assumption

        # We can skip the case svar == var, as var: EVar

        # We know that some instances of var are substituted
        # so we need to check both pattern and plug
        # Pattern contains instances of var, but this won't affect s_fresh(svar)
        # (see explanation for e_fresh)
        return pattern.s_fresh(svar) and plug.s_fresh(svar) # fresh-after-subst

    # Best-effort for now, as we can't handle (pattern.positive(var) returns something else
    # than intended, as positive takes set variable, not var: EVar)
    def positive(svar):
        # Both pattern and plug need to be checked, as
        # the substitution is well-formed by assumption
        # and svar != var in ESubst

        # Note that the unsubstituted var in pattern
        # do not influence the result, as var: EVar

        # If svar notin FV(plug), so plug has no influence on the result

        return pattern.positive(svar) and plug.s_fresh(svar)

    # Best-effort for now, as we can't handle (pattern.positive(var) returns something else
    # than intended, as positive takes a set variable, not var: EVar)
    def negative(svar):
        # Both pattern and plug need to be checked, as
        # the substitution is well-formed by assumption
        # and svar != var in ESubst
        # Note that the unsubstituted var in pattern
        # do not influence the result, as var: EVar
        return pattern.negative(svar) and plug.s_fresh(svar)

class SSubst(Pattern):
    pattern: MetaVar | SSubst | ESubst
    var: u8
    plug: Pattern

    def well_formed():
        # We do not allow redundant substitutions, since it reduces need the meta-inference for freshness etc.
        if var == plug:           return False  # This is the identity substitution, and so is redundant.
        if pattern.s_fresh(var):  return False  # The variable does not occur, so this is redundant
        # Now we know at least one set variable will be substituted, so we need to check
        # well-formedness of both pattern and plug
        return pattern.well_formed() and plug.well_formed()

    def e_fresh(evar):
        # We can skip the case pattern.s_fresh(var) == true, as
        # such a substitution is malformed by assumption

        # We can skip the case evar == var, as var: SVar

        # We know that some instances of var are substituted
        # so we need to check both pattern and plug
        # Pattern contains instances of var, but this won't affect e_fresh(evar)
        # (see explanation for s_fresh)
        return pattern.e_fresh(evar) and plug.e_fresh(evar) # fresh-after-subst

    def s_fresh(svar):
        # We can skip the case pattern.e_fresh(var) == true, as
        # such a substitution is malformed by assumption

        if svar == var:
            # This means there are free instances of svar == var and all of them
            # are being substituted for plug, so its freshness depends on plug
            return plug.s_fresh(svar)       # fresh-in-subst

        # There are free instances of var being substituted and svar != var, so
        # we need to check for freshness of svar in both the original pattern
        # and the plugged pattern
        # Note that it's fine that the original pattern still contains
        # free instances of var => we know that those won't affect
        # the result as svar != var
        return pattern.s_fresh(svar) and plug.s_fresh(svar) # subst-after-subst

    # Note that the case where occurence of svar is positive in SSubst by some paths being positive by pat.pos + plug.pos
    # and some paths being positive by pat.neg + plug.neg cannot happen, as plug is fixed and we're checking for plug.s_fresh(svar)!
    # Consider such a scenario can happen for a contradiction:
    # then svar has a negative occurrence by the simple fact that plug contains
    # at least one free instance of svar, contradiction with assuming all occurrences of svar in the result are positive
    def positive(svar):
        plug_positive_svar =
                plug.s_fresh(svar) # svar notin FV(plug), so plug has no influence on the result
            or  pattern.positive(var) and plug.positive(svar)
            or  pattern.negative(var) and plug.negative(svar)

        if svar == var:
            # All free occurrences of svar are being replaced with plug,
            # so positivity only depends on plug
            return plug_positive_svar

        # Both pattern and plug need to be checked, as
        # the substitution is well-formed by assumption so
        # there is at least one occurrence of var being replaced

        # Note that the unsubstituted var in pattern
        # does not influence the result, as svar != var
        return pattern.positive(svar) and plug_positive_svar

    # For a sketch of correctness, see comment on positive(svar)
    def negative(svar):
        plug_negative_svar =
                plug.s_fresh(svar)
            or  pattern.positive(var) and plug.negative(svar)
            or  pattern.negative(var) and plug.positive(svar)

        if svar == var:
            # All free occurrences of svar are being replaced with plug,
            # so negativity only depends on plug
            return plug_negative_svar

        # Both pattern and plug need to be checked, as
        # the substitution is well-formed by assumption so
        # there is at least one occurrence of var being replaced

        # Note that the unsubstituted var in pattern
        # does not influence the result, as svar != var
        return pattern.negative(svar) and plug_negative_svar
```


`Proof`s
--------

### Axiom Schemas

Axiom schemas are `Proof`s that do not need any input arguments.
They may use `MetaVar`s to represent their schematic nature.

```python
class Lukasiewicz(Proof):
    def conclusion():
        phi1 = MetaVar('phi1')
        return Implies(Implies(Implies(MetaVar(phi1) , ...)...)...)

class Quantifier(Proof):
    def conclusion():
        x = EVar('#x')
        y = EVar('#y')
        phi = MetaVar('phi', fresh=[y])
        return Implies(ESubst(phi, x, y), Exists(x, phi))

class PropagationOr(Proof):
    def conclusion():
        hole = EVar('#hole')
        C = MetaVar(app_ctx_holes=(EVar('#hole'),))
        phi1 = MetaVar('#phi1')
        phi2 = MetaVar('#phi2')
        return Implies(ESubst(C, or(phi1, phi2), hole), or(ESubst(C, phi1, hole), ESubst(C, phi2, hole)))

...
```


### Meta Variable Instantiation

Using a rule of meta inference, we may instantiate metatheorems.
This allows us to instantiate axiom and theorem schemas, such as
$\phi \limplies \phi$.
For performance and convenience reasons, we support *simultaneous* instantiations
that can instantiate several metavars at once, where all pluggings are isolated (they do
not cause side-effects among each other).
This means:

```
    (0 -> 1)[0 |-> (0 -> 1), 1 |-> 2]
~>  ((0 -> 1) -> 2)
```

As one can see, the metavar with id `1` replaced .
Multiple instantiations in a sequence are common, and this makes them much
simpler to perform without the need to introduce any fresh names to prevent these
side-effects.
Moreover, only *one* well-formedness check is needed afterwards, which can save
lots of execution cycles.
Conventional sequential instantiations are still trivially supported in the
obvious way.
Here's the blueprint:


```python
class InstantiateSchema(Proof):
    subproof : Proof
    metavar_ids: list(u8)
    instantiations: list(Pattern)

    def well_formed():
        for metavar in subproof.conclusion().metavars():
            if metavar.id not in metavar_ids:
                continue

            pattern = instantiations[metavar_ids.index(metavar.id)]

            for evar in metavar.e_fresh:
                if not pattern.e_fresh(evar):
                    return False
            for svar in metavar.s_fresh:
                if not pattern.s_fresh(svar):
                    return False
            for svar in metavar.positive:
                if not pattern.positive(svar):
                    return False
            for svar in metavar.negative:
                if not pattern.negative(svar):
                    return False
            for evar in metavar.app_ctx_holes:
                if not pattern.app_ctx_holes(evar):
                    return False

        return len(metavar_ids) == len(instantiations)

    def conclusion():
        return subproof.conclusion().meta_substitute(metavar_ids, instantiations)
```

TODO: Could we just merge this with `InstantiateSchema`?
We may also use metavariables to represent notation.

```python
class InstantiateNotation(Pattern):
    notation: Pattern
    metavar_ids: list(u8)
    instantiations: list(Pattern)

    def well_formed():
        for metavar in notation.metavars():
            if metavar.id not in metavar_ids:
                continue

            for evar in metavar.e_fresh:
                if not notation.e_fresh(evar):
                    return False
            for svar in metavar.s_fresh:
                if not notation.s_fresh(svar):
                    return False
            for svar in metavar.positive:
                if not notation.positive(svar):
                    return False
            for svar in metavar.negative:
                if not notation.negative(svar):
                    return False
            for evar in metavar.app_ctx_holes:
                if not notation.app_ctx_holes(evar):
                    return False

        return len(metavar_ids) == len(instantiations)

    def conclusion():
        return notation.meta_substitute(metavar, instantiation)
```


### Ordinary inference

```python
class ModusPonens(Proof):
    premise_left: Implies
    premise_right: Pattern

    def conclusion():
        return premise_left.right

    def well_formed():
        assert premise_right == premise_left.left

class Generalization(Proof):
    premise: Implies

    def phi1():
        premise.left
    def phi2():
        premise.right

    def conclusion():
        return Implies(ESubst(MetaVar(phi), EVar(x), EVar(y)), Exists(EVar(x), MetaVar(phi)))

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

### Variables and Symbols:

`EVar <u8>`
:   Push an `EVar` onto the stack.

`SVar <u8>`
:   Push a `SVar` onto the stack.

`Symbol <u8>`
:   Push a `Symbol` onto the stack.

`Implies`/`App`
:   Consume the two patterns from the stack,
    and push an implication/application to the stack
    with appropriate arguments.

`Exists <var_id:u8>`/`Mu <var_id:u8>`
:   Consume a pattern from the stack, and push the corresponding pattern to the stack, if well-formed.

### Axiom Schemas

`Lukasiewicz`/`Quantifier`/`PropagationOr`/`PropagationExists`/`PreFixpoint`/`Existance`/`Singleton`
:   Push proof term corresponding to axiom schema onto the stack.

### Meta inference

`MetaVar <id:u8, 5 * (len: u8, constraint: [u8] * len)`
:   Push an `MetaVar` onto the stack.

`ESubst <metavar_id:u8>`/`SSubst <metavar_id:u8>`
:   Consume a meta-pattern `phi` and a pattern `psi` from the stack, and push a
    corresponding substitution `phi[psi/metavar_id]`.

`Instantiate n:u8 [metavar_id:u8]*n`
:   Consume a `Proof` and then n `Pattern`s off the stack, and push the instantiated proof term to the stack,
    checking wellformedness as needed.

### Inference rules

`ModusPonens`/`Generalization`/`Frame`/`Substitution`/`KnasterTarski`
:   Consume one or two `Proof` terms off the stack and push the new proof term.

### Memory manipulation:

`Save`
:   Store the top element of the stack by appending it to the memory array.

`Load <i:u8>`
:   Push the `Term` at index $i$ in memory to the top of the stack.


### Journal manipulation.

`Publish`
:   * During the `gamma` phase, consume a pattern from the stack and push it to the list of axioms.
    * During the `claim` phase consume a pattern from the stack and push it to the stack of claims.
    * During the `proof` phase consume a proof from the stack
      and a claim from the queue of claims and assert that they are equal.

    Note that since the claims form a stack, they must be proved in the reverse order they
    were declared in[^claims-stack-vs-queue].

[^claims-stack-vs-queue]: This is convenient for the current implementation, but we may want to revist it later.

### Stack manipulation.

`Pop`
:   Consume the top of the stack.

### Technical

Notation
========

Our format does not use an explicit concept for notation, but merely
a convention that proof generation tools utilize to shorten proofs.

Notation at the ADT level
-------------------------

At the ADT level, notation are just saved meta-patterns.
We use instantiations to use concrete instances of notation.
For example,

```
bot = Mu(0, SVar(0))
negation = Implies(MetaVar(0), bot) = Implies(MetaVar(0), Mu(0, SVar(0)))
top = Instantiate(negation, 0, bot) = Instantiate(Implies(MetaVar(0), Mu(0, SVar(0))), 0, Mu(0, SVar(0)))
```

Notation at the DAG level
-------------------------

Notice, in the above specification `bot` is used twice in the definition of `top`.
Consider the tree representation of top:

```
              SVar(0)        SVar(0)
                 |              |
  MetaVar(0)    Mu(0)          Mu(0)
       |         |              |
       \        /              /
        \      /              /
         Implies             /
             \              /
              \            /
               Instantiate(0)
```

In a DAG we can re-use a sub-tree to reduce this redundancy.

```
                 SVar(0)
                   |
                  Mu(0)
                   |   \
                   |    \
                   |     \
      MetaVar(0)   |     |
            \      |     |
             Implies     |
                 \       |
                  \      |
               Instantiate(0)
```


Notation at the Binary representation level
-------------------------------------------

The `Save` and `Load` instructions allow us to share these reused subterms.


Future considerations
=====================

-   De Bruijn-like nameless representation: A nameless representation would
    simplify substitution and well-formedness checking.
-   Since we are constructing an on-the-wire format for machine use, there are
    other nameless representations we may consider. For example, we can consider
    two variables (element, set, meta-) equal, only if they are the identical
    DAG node. That is, the variable was constructed once, and retrieved using
    the `Load` command.

