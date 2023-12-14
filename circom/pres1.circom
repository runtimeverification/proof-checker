pragma circom 2.1.0;

/*
Part 1

Circom is a DSL for generating something called Rank-1-Constraint-Systems, which we'll get to later.
But first, let's consider Circom as a DSL for generating arithmetic circuits of the following kind. 
- Each gate is either input, output or intermediate.
- Intermediate gates are sum or multiplication of exactly two arguments (gates or constants).
- Operations are taking place modulo a prime P (usually ~256 bits long)
*/

// Let's evaluate the multivariate polynomial:
// F(x, y) = 3x^2 + xy

template EvalF() {
    signal input x;
    signal input y;
    signal output result;

    signal xsquared <== x * x;
    signal xsquared_3 <== 3 * xsquared;

    signal xy <== x * y;
    
    result <== xsquared_3 + xy;
} 

component main = EvalF();