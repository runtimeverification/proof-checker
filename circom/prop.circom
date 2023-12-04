pragma circom 2.1.0;

/* TODO
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

template EqConst(C) {
    signal input x;
    signal output out;

    out <== IsZero()(x - C);
}

template NOT() {
    signal input in;
    signal output out;

    out <== 1 + in - 2*in;
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

template MultiOR(n) {
    signal input in[n];
    signal not_in[n];
    signal output out;

    for (var i = 0; i < n; i ++) {
        not_in[i] <== NOT()(in[i]);
    }

    var and_res = MultiAND(n)(not_in);
    out <== NOT()(and_res);
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
    signal check_size;
    signal output out;
    
    // Check necessary ->
    //signal implications = AND()()
    //assert(pattern[0] == 1);
    //assert(pattern[A_LEN + 1] == 1);

    component checker = ArrEq (A_LEN);
    for (var i = 0; i < A_LEN; i ++) {
        checker.a[i] <== pattern[i + 1];
        checker.b[i] <== pattern[i + 2 + A_LEN + B_LEN];
    }

    check_size <== SizeChecker(M, 2 + 2 * A_LEN + B_LEN)(pattern);

    out <== AND()(checker.out, check_size);
}

template Prop1 (M) {
    signal input pattern[M];
    signal output out;

    component fixedProp[M][M];
    var lenA = 0, lenB = 0, solutions = 0;

    for (lenA = 1; lenA < M; lenA++) {
        for (lenB = 1; lenB < M; lenB++) {
            if (2 + 2 * lenA + lenB <= M) {
                var sol = Prop1FixedLen(M, lenA, lenB)(pattern);
                solutions += sol;
            }
        }
    }

    solutions ==> out;
}

// Recognize ->->A->BC->->AB->AC

template Prop2FixedLen (M, A_LEN, B_LEN, C_LEN) {
    signal input pattern[M];
    signal size_check;
    signal output out;

    // Check necessary ->
    /*
    assert(pattern[0] == 0);
    assert(pattern[1] == 0);
    assert(pattern[1 + 1 + A_LEN] == 0);
    assert(pattern[1 + 1 + A_LEN + 1 + B_LEN + C_LEN] == 0);
    assert(pattern[1 + 1 + A_LEN + 1 + B_LEN + C_LEN + 1] == 0);
    assert(pattern[1 + 1 + A_LEN + 1 + B_LEN + C_LEN + 1 + 1 + A_LEN + B_LEN] == 0);
    */

    component a_checker[2];

    a_checker[0] = ArrEq(A_LEN);
    for (var i = 0; i < A_LEN; i ++) {
        a_checker[0].a[i] <== pattern[2 + i];
        a_checker[0].b[i] <== pattern[5 + A_LEN + B_LEN + C_LEN + i];
    }

    a_checker[1] = ArrEq(A_LEN);
    for (var i = 0; i < A_LEN; i ++) {
        a_checker[1].a[i] <== pattern[2 + i];
        a_checker[1].b[i] <== pattern[6 + 2 * A_LEN + 2 * B_LEN + C_LEN + i];
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

    size_check <== SizeChecker(M, 6 + 3 * A_LEN + 2 * B_LEN + 2 * C_LEN)(pattern);
    out <== MultiAND(5)([a_checker[0].out, a_checker[1].out, b_checker.out, c_checker.out, size_check]);
}

// Recognize ->->A->BC->->AB->AC

template Prop2 (M) {
    signal input pattern[M];
    signal output out;

    var solutions = 0;
    for (var lenA = 1; lenA < M; lenA++)
        for (var lenB = 1; lenB < M; lenB++) 
            for (var lenC = 1; lenC < M; lenC++) {
                if (6 + 3 * lenA + 2 * lenB + 2 * lenC <= M) {
                    var sol = Prop2FixedLen(M, lenA, lenB, lenC)(pattern);
                    solutions += sol;
                }
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
    // assert (premise[1][0] == 1);

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

    out <== EqConst(1)(solutions);
}



// N - is the number of steps in the proof
// M - the maximum length of a single step/pattern

// patterns: "a" = [2], "->aa" = [1, 2, 2]

// (conclusion pattern, i, j) => (conclusion, premise1, premise2)
// access proof[i] when i is dynamic
// to access a[x], where both a[] and x are inputs:
// a[x] = [Sum over a[i] * EqConst(i, x)]
// EqConst(i, x) = 0 if x != i
// EqConst(i, x) = 1 if x == i

// string str[], h(str) = Sum str[i] * X ^ i, h(str)(R)
// 

template CheckProof (N, M) {
    signal input proof[N][M];
    signal input annotations[N][2];
    signal output out;

    signal premise[N][2][M];
    signal valid[N];

    signal coefs[N][N][2];
    signal inter[N][N][M][2];
    //TODO^ why is inter necessary?

    var i = 0, j = 0, k = 0, p = 0, correct = 0;

    for (i = 0; i < N; i++) {
        var premise_arr[2][M];

        for (p = 0; p < 2; p++) 
            for (k = 0; k < M; k++) 
                premise_arr[p][k] = 0;
        
        for (p = 0; p < 2; p++)
            for (j = 0; j < i; j++) {
                coefs[i][j][p] <== EqConst(j)(annotations[i][p]);
                for (k = 0; k < M; k++) {
                    inter[i][j][k][p] <== proof[j][k] * coefs[i][j][p];
                    premise_arr[p][k] += inter[i][j][k][p];
                }
            }

        for (p = 0; p < 2; p++) {
            for (k = 0; k < M; k++) {
                premise[i][p][k] <== premise_arr[p][k];
            }
        }

        log();
        for (var lp = 0; lp < 2; lp++) {
            for (var l = 0; l < M; l++) {
                log(premise[i][lp][l]);
            }
            log();
        }

        var check_MP = ModusPonens(M)(premise[i], proof[i]);
        var check_Prop1 = Prop1(M)(proof[i]);
        var check_Prop2 = Prop2(M)(proof[i]);

        valid[i] <== MultiOR(3)([check_MP, check_Prop1, check_Prop2]);
    }

    for (i = 0; i < N; i++) {
        log("Validity of step", i, ":", valid[i]);
    }

    out <== MultiAND(N)(valid);
    out === 1;
}

/*
1. ->->p->->ppp->->p->pp->pp
2. ->p->->ppp
3. ->->p->pp->pp
4. ->p->pp
5. ->pp
*/