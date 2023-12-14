pragma circom 2.1.0;

/*
Part 3

Rank-1-Constraint-Systems.

A valid R1-CS constraint looks like this:



template NOT() {
    signal input a;
    signal output result;

    result <== 1 - a;
    // -a is easily desugared to (P - a)
}

template AND() {
    signal input a;
    signal input b;
    signal output result;

    result <== a * b;
}

template OR() {
    signal input a;
    signal input b;
    signal output result;

    // result<== ??;
}

// Parameter: constant N, known at compile-time
// Input: binary array "a" of size N;
// Result: Logical OR of values in "a" 

template MultiOR(N) {
    signal input a[N];
    signal part[N];
    signal output result;

    for (var i = 0; i < N; i++) {
        if (i == 0) {
            part[i] <== a[i];
        } else {
            part[i] <== OR()(part[i - 1], a[i]);
        }
    }

    result <== part[N - 1];
}

// Input: binary values: a, b, flag
// Output: (a AND b) if flag is 1, (a OR b) otherwise

template If_expr() {
    signal input a;
    signal input b;
    signal input flag;

    signal and <== AND()(a, b);
    signal or <== OR()(a, b);
    signal not_flag <== NOT()(flag);

    signal and_option <== flag * and;
    signal or_option <== not_flag * or;

    signal output result <== and_option + or_option; 
}

/*
Input: arbitrary integer a;
Output: 1 if a == 0 and 0 otherwise

We use Fermat's theorem which states that if P is prime, then:
forall x > 0, x ^ (P - 1) = 1 (mod P)

Obviously, x ^ (P - 1) = 0 if x == 0.

So we want to return 1 - (x ^ (P - 1)).

Actual prime used by circom is huge so let's assume it's actually 17 so we can compile :).
*/


template IsZeroSlow() {
    //var actual_p = 21888242871839275222246405745257275088548364400416034343698204186575808495617;
    signal input x;
    signal output result;
    signal part[17];


    part[0] <== 1;

    for (var i = 1; i < 17; i ++) {
        part[i] <== part[i - 1] * x;
    }

    result <== 1 - part[16];
}

// Parameter: C
// Input: a
// Result: 1 if a == C, 0 otherwise

template EqConst(C) {
    signal input a;
    signal output result;

    result <== IsZeroSlow()(a - C);
}

// Parameter: constant N, known at compile-time
// Input: Array "a" of size N;
// Input: Integer "index" assumed to be < N;
// Result: Value of a[index] 

template Load(N) {
    signal input a[N];
    signal input index;
    signal term[N], coef[N], part[N];
    signal output result;

    for (var i = 0; i < N; i++) {
        coef[i] <== EqConst(i)(index);
        term[i] <== a[i] * coef[i];
        if (i == 0) {
            part[i] <== a[i];
        } else {
            part[i] <== part[i - 1] + term[i];
        }
    }

    result <== part[N - 1];
}

component main = Load(5);