pragma circom 2.1.0;

/* TODO
- Check pattern lengths
- Check wellformed-ness
*/

template IsZero() {
    signal input in_;
    signal output out;
    signal inv;
    inv <-- in_!=0 ? 1/in_ : 0;
    out <== -in_*inv +1;
    in_*out === 0;
}

template AND() {
    signal input a;
    signal input b;
    signal output out;

    out <== a*b;
}

template MultiAND(n) {
    signal input in[n];
    signal output out;
    component and1;
    component and2;
    component ands[2];
    if (n==1) {
        out <== in[0];
    } else if (n==2) {
        and1 = AND();
        and1.a <== in[0];
        and1.b <== in[1];
        out <== and1.out;
    } else {
        and2 = AND();
        var n1 = n\2;
        var n2 = n-n\2;
        ands[0] = MultiAND(n1);
        ands[1] = MultiAND(n2);
        var i;
        for (i=0; i<n1; i++) ands[0].in[i] <== in[i];
        for (i=0; i<n2; i++) ands[1].in[i] <== in[n1+i];
        and2.a <== ands[0].out;
        and2.b <== ands[1].out;
        out <== and2.out;
    }
}

template SizeChecker (M, EXPECTED_LEN) {
    signal input pattern[M];
    signal temp[M];
    signal output out;

    for (var i = 0; i < M; i++) {
        var is_zero = IsZero()(pattern[i]);
        if (i < EXPECTED_LEN)
            temp[i] <== 1 - is_zero;
        else 
            temp[i] <== is_zero;
    }

    out <== MultiAND(M)(temp);
}

// Check that array a coincides with array b
template ArrEq (N) { 
    signal input a[N];
    signal input b[N];
    signal partial[N];
    signal output out;

    component IsZero_[N];

    for (var i = 0; i < N; i++) {
        IsZero_[i] = IsZero();
        IsZero_[i].in_ <== (a[i] - b[i]);
        if (i == 0) {
            partial[i] <== IsZero_[i].out;
        } else {
            partial[i] <== partial[i - 1] * IsZero_[i].out;
        }
    } 

    partial[N - 1] ==> out;
}

// Recognize ->A->BA

template Prop1FixedLen (M, A_LEN, B_LEN) {
    signal input pattern[M];
    signal output out;
    
    // Check necessary ->
    assert(pattern[0] == 1);
    assert(pattern[A_LEN + 1] == 1);

    component checker = ArrEq (A_LEN);
    for (var i = 0; i < A_LEN; i ++) {
        checker.a[i] <== pattern[i + 1];
        checker.b[i] <== pattern[i + 2 + A_LEN + B_LEN];
    }

    out <== checker.out;
}

template Prop1 (M) {
    signal input pattern[M];
    signal output out;

    component fixedProp[M][M];
    var lenA = 0, lenB = 0, solutions = 0;

    for (lenA = 1; lenA < M; lenA++) {
        for (lenB = 1; lenB + 2 * lenA + 2 < M; lenB++) {
            var sol = Prop1FixedLen(M, lenA, lenB)(pattern);
            solutions += sol;
        }
    }

    solutions ==> out;
}

// Recognize ->->A->BC->->AB->AC

template Prop2FixedLen (M, A_LEN, B_LEN, C_LEN) {
    signal input pattern[M];
    signal output out;

    // Check necessary ->
    assert(pattern[0] == 0);
    assert(pattern[1] == 0);
    assert(pattern[1 + 1 + A_LEN] == 0);
    assert(pattern[1 + 1 + A_LEN + 1 + B_LEN + C_LEN] == 0);
    assert(pattern[1 + 1 + A_LEN + 1 + B_LEN + C_LEN + 1] == 0);
    assert(pattern[1 + 1 + A_LEN + 1 + B_LEN + C_LEN + 1 + 1 + A_LEN + B_LEN] == 0);

    component a_checker[2];

    a_checker[0] = ArrEq(A_LEN);
    for (var i = 0; i < A_LEN; i ++) {
        a_checker[0].a[i] <== pattern[2 + i];
        a_checker[0].b[i] <== pattern[5 + A_LEN + B_LEN + C_LEN + i];
    }

    a_checker[1] = ArrEq(A_LEN);
    for (var i = 0; i < A_LEN; i ++) {
        a_checker[0].a[i] <== pattern[2 + i];
        a_checker[0].b[i] <== pattern[6 + 2 * A_LEN + 2 * B_LEN + C_LEN + i];
    }

    component b_checker = ArrEq(B_LEN);
    for (var i = 0; i < B_LEN; i ++) {
        b_checker.a[i] <== pattern[3 + A_LEN + i];
        b_checker.b[i] <== pattern[5 + 2 * A_LEN + B_LEN + C_LEN + i];
    }

    component c_checker = ArrEq(C_LEN);
    for (var i = 0; i < C_LEN; i ++) {
        c_checker.a[i] <== pattern[3 + A_LEN + B_LEN + i];
        c_checker.b[i] <== pattern[6 + 3 * A_LEN + 2 * B_LEN + C_LEN + i];
    }

    out <== MultiAND(4)([a_checker[0].out, a_checker[1].out, b_checker.out, c_checker.out]);
}


template Prop2 (N) {
    signal input pattern[N];
    signal output out;

    var solutions = 0;
    for (var lenA = 1; lenA < N; lenA++)
        for (var lenB = 1; lenB < N; lenB++) 
            for (var lenC = 1; lenC < N; lenC++) {
                var sol = Prop2FixedLen(N, lenA, lenB, lenC)(pattern);
                solutions += sol;
        }

    solutions ==> out;
}

// Check ModusPonens instance:
// Premise 0: A
// Premise 1: ->AB
// Conclusion: B

template ModusPonensFixedLen (M, A_LEN, B_LEN) {
    signal input premise[2][M];
    signal input conclusion[M];
    signal output out;

    // Check Premise 1 is an implication
    assert (premise[1][0] == 1);

    component check_0 = ArrEq(A_LEN);
    for (var i = 0; i < A_LEN; i++) {
        check_0.a[i] <== premise[0][i];
        check_0.b[i] <== premise[1][1 + i];
    }

    component check_1 = ArrEq(B_LEN);
    for (var i = 0; i < B_LEN; i++) {
        check_1.a[i] <== conclusion[i];
        check_1.b[i] <== premise[1][1 + A_LEN + i];
    }

    var size_a = SizeChecker(M, A_LEN)(premise[0]);
    var size_ab = SizeChecker(M, 1 + A_LEN + B_LEN)(premise[1]);
    var size_b = SizeChecker(M, B_LEN)(conclusion);

    out <== MultiAND(5)([
        check_0.out, 
        check_1.out,
        size_a,
        size_ab,
        size_b
    ]);
}

// Check ModusPonens instance:
// Premise 0: A
// Premise 1: ->AB
// Conclusion: B

template ModusPonens (M) {
    signal input premise[2][M];
    signal input conclusion[M];
    signal output out;

    var solutions = 0;
    for (var lenA = 1; lenA < M; lenA++)
        for (var lenB = 1; lenB < M; lenB++) {
                if (lenA + lenB + 1 <= M) {
                    var sol = ModusPonensFixedLen(M, lenA, lenB)(premise, conclusion);
                    solutions += sol;
                }
        }

    solutions === 1;
}

component main = ModusPonens(5);