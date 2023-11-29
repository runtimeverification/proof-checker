pragma circom 2.0.0;

// Check that array a coincides with array b

template ArrEq (N) { 
    signal input a[N];
    signal input b[N];
    signal partial[N];
    signal output out;

    for (var i = 0; i < N; i++) {
        var eq = (a[i] == b[i]) ? 1 : 0;
        if (i == 0) {
            partial[i] <== eq;
        } else {
            partial[i] <== partial[i - 1] * eq;
        }
    } 

    partial[N - 1] ==> out;
}


// Check that you can apply modus ponens on A and B to obtain C,
// i.e that B is of the form (A -> C)

template ModusPonensFixedLen (MAXLEN, A_LEN, C_LEN) {
    signal input premises[2][MAXLEN];
    signal input conclusion[MAXLEN];
    signal output out;
    var i = 0;

    assert (premises[1][0] == 1);

    component check_premise = ArrEq(A_LEN);
    premises[0][MAXLEN] ==> check_premise.a;
    for (i = 1; i <= A_LEN; i++) {
        check_premise.b[i - 1] = premises[1][i];
    }

    component check_conclusion = ArrEq(MAXLEN);
    conclusion ==> check_conclusion.A;

    for (i = 1 + A_LEN; i < MAXLEN; i++) {
        check_conclusion.b[i - 1] = premises[1][i];
    }

    out <== check_premise.out * check_conclusion.out;
}

template ModusPonens (MAXLEN) {
    signal input premises[2][MAXLEN];
    signal input conclusion[MAXLEN];
    signal output out;
}

// Checks that pattern is instantiation of (A -> (B -> A))
// Prefix-form: ->A->BA

// ->1->2100000000
// ->->12->3->1200

template Prop1FixedLen (N, A_LEN) {
    signal input pattern[N];
    signal output out;
    
    // Check necessary ->
    assert(pattern[0] == 0);
    assert(pattern[A_LEN + 1] == 0);

    component checker = SubseqEq(N, 1, N - A_LEN, A_LEN);
    checker.str <== pattern;
    out <== checker.out;
}

template Prop1 (N) {
    signal input pattern[N];
    signal output out;

    component fixedSubs[N / 2 + 1];
    var lenA = 0, solutions = 0;

    for (lenA = 1; 2 * lenA + 1 < N; lenA++) {
        fixedSubs[lenA] = Prop1FixedLen(N, lenA);
        pattern ==> fixedSubs[lenA].pattern;
        solutions += (1 - fixedSubs[lenA].out);
    }

    solutions ==> out;
}

// Checks that pattern is instantiation of [A -> (B -> C)] -> [(A -> B) -> (A -> C)]
// Postfix-form: ->->A->BC->->AB->AC

template Prop2FixedLen (N, A_LEN, B_LEN) {
    signal input pattern[N];
    signal output out;
    
    // Infer C_LEN
    var C_LEN = (N - 6 - 2 * A_LEN - 2 * B_LEN) / 2;

    // Check necessary ->
    assert(pattern[0] == 0);
    assert(pattern[1] == 0);
    assert(pattern[1 + 1 + A_LEN] == 0);
    assert(pattern[1 + 1 + A_LEN + 1 + B_LEN + C_LEN] == 0);
    assert(pattern[1 + 1 + A_LEN + 1 + B_LEN + C_LEN + 1] == 0);
    assert(pattern[1 + 1 + A_LEN + 1 + B_LEN + C_LEN + 1 + 1 + A_LEN + B_LEN] == 0);

    component a_checker[2];
    a_checker[0] = SubseqEq(N, 2, 5 + A_LEN + B_LEN + C_LEN, A_LEN);
    a_checker[0].str <== pattern;
    a_checker[1] = SubseqEq(N, 2, 6 + 2 * A_LEN + 2 * B_LEN + C_LEN, A_LEN);
    a_checker[1].str <== pattern;

    component b_checker;
    b_checker = SubseqEq(N, 3 + A_LEN, 5 + 2 * A_LEN + B_LEN + C_LEN, B_LEN);
    b_checker.str <== pattern;

    component c_checker;
    c_checker = SubseqEq(N, 3 + A_LEN + B_LEN, 6 + 3 * A_LEN + 2 * B_LEN + C_LEN, C_LEN);
    c_checker.str <== pattern;

    out <== a_checker[0].out * a_checker[1].out * b_checker.out * c_checker.out;
}

template Prop2 (N) {
    signal input pattern[N];
    signal output out;

    component fixedSubs[N / 2 + 1][N / 2 + 1];
    var lenA = 0, lenB = 0, solutions = 0;

    for (lenA = 1; lenA < N; lenA++)
        for (lenB = 1; lenB < N; lenB++) {
            fixedSubs[lenA][lenB] = Prop2FixedLen(N, lenA, lenB);
            pattern ==> fixedSubs[lenA][lenB].pattern;
            solutions += (1 - fixedSubs[lenA][lenB].out);
        }

    solutions ==> out;
}

// Checks a proof consisting of N annotated patterns. The patterns have length at most MAXLEN

/*
(PATTERN, i, j)
(PATTERN, 0, 1)
(PATTERN, 0, 2) */

template CheckProof (N, MAXLEN) {
    signal input proof[(N + 1)][(MAXLEN + 2)];
    signal output out;
    
    /*
    var x = 7;
    signal input y;

    proof[x] // works
    proof[y] // doesn't work => different circuit structures for different inputs

    signal proof_y = Sum over [(proof[i]) * Equality(y, i).out] // == proof[y]

    // N == 2
    // proof[y] = proof[1] * Equality(y, 1).out + proof[2] * Equality(y, 2).out


    signal premise[N][2][MAXLEN];
    // premise[i][j] = the j-th premise of step i (an array of MAXLEN)
    // */

    signal is_correct1[N];

    component MP_[N];
    component Prop1_[N];
    component Prop2_[N];

    var i = 0, j = 0, k = 0, p = 0, correct = 0;

    for (i = 0; i < N; i ++) {
        MP_[i] = ModusPonens(N);
        Prop1_[i] = Prop1(N);
        Prop2_[i] = Prop2(N);
    }

    for (i = 0; i < N; i++) {
        var premise_arr[2][MAXLEN];

        for (p = 0; p < 2; p++) 
            for (k = 0; k < MAXLEN; k++) 
                premise_arr[p][k] = 0;
        
        for (p = 0; p < 2; p++)
            for (j = 0; j < i; j++)
                for (k = 0; k < MAXLEN; k++) {
                    var coef = (j == proof[i][MAXLEN + p]) ? 1 : 0;
                    premise_arr[p][k] += proof[j][k] * coef;
                }

        for (p = 0; p < 2; p++) {
            for (k = 0; k < MAXLEN; k++) {
                premise[i][p][k] <== premise_arr[p][k];
            }
        }

        MP_[i].premises <== premise[i]; 
        for (j = 0; j < MAXLEN; j++) {
            MP_[i].conclusion[j] <== proof[i][j];
            Prop1_[i].pattern[j] <== proof[i][j];
            Prop2_[i].pattern[j] <== proof[i][j];
        }

        is_correct1[i] <== (1 - MP_[i].out) * (1 - Prop1_[j].out);
        var is_correct2 = is_correct1[i] * (1 - Prop2_[i].out); 
        correct += (1 - is_correct2);
    }

    out <== correct;
    correct === N;
}

component main = CheckProof(10, 5);