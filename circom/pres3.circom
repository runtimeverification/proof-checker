pragma circom 2.1.0;

/*
Part 3

Rank-1-Constraint-Systems.

A valid R1CS constraint looks like this:

(a DOT x) * (b DOT x) = (c DOT x) (mod P)

- DOT is the dot-product ([a, b] DOT [c, d] = a * c + b * d)
- a, b, c are arrays of constants
- x is an array of variables (or possibly the constant 1)

Examples:

(3x + 5y + 1)(4x + 6) = 25y
3x + 5 = 0
4x^2 + 4x + 1 == y
^^^
(2x + 1)(2x + 1) == y


A R1CS instance is a set of several such constraints.

There exist SNARK backends (e.g PLONK) which can produce a succinct proof of a valid solution to a R1CS.
The goal is to express computation as R1CS.

For example, note that R1CS can express arithmetic circuits, by assigning variables to gates and 
enforcing gate types by using constraints:

// result as a SUM gate
x + y - result == 0


// result as a PRODUCT gate
x * y - result == 0

x^3 == 0

as R1CS:

a = 0
a = b * x
b = x * x

The Circom compiler actually generates R1CS, along with hints on how to satisfy them.

*/

template Example() {
    signal input x;
    signal output y;

    // Computation.
    // This is what the prover should do to compute y
    y <-- 2 * x;
    // Constraint:
    // This is what ends up in the R1CS and needs to be satisfied
    y === 2 * x;

    // Equivalently and most often used in Circom:   
     y <=== 2 * x;
}

/*
Are there notable situations where computation and constraint differ considerably?
*/

/* 
Yes! 
Here's IsZero written in 2 constraints.
*/

template IsZero() {
    signal input x;
    signal output out;
    signal inv;

    // Computation uses modular division, 
    // It can do so because it's performed outside
    // the constraint system
    inv <-- x !=0 ? 1/x : 0;

    // Constraint 1
    out <== 1 - x*inv ;
    // Constraint 2 
    x*out === 0;

    // If (x, out) = (0, 1) both constraints are met, regardless of inv
    // If (x, out) = (0, 0) Constraint 1 cannot be satisfied, regardless of inv
    // If (x, out) = (>0, 1) Constraint 2 is not satisfied, regardless of inv
    // If (x, out) = (>0, 0) Constraint 2 is satisfied, Constraint 1 CAN be satisfied by choosing inv = x ^(-1)
}

/*
More generally, we can try to provide SPECS for computations which are easier to verify in R1CS
than the computation itself.

Another example is sorting, which can be specified as:
- Input and output are identical as multisets
- Output is ordered

Checking these properties is less expensive than sorting itself (by a factor of log N!).

SIDE-COMMENT: 
The thought process resembles formal verification.
If there will exist a sizable market for developing verifiable computation via constraint systems,
we might be in a prime position to consult/audit such projects. 
*/

component main = IsZero();