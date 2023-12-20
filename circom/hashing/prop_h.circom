pragma circom 2.1.0;

/* TODO
- Implement Prop3
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

// Checks that the pattern actually has EXPECTED_LEN (although it is encoded as an array of length M)
// <-> First EXPECTED_LEN chars are non-zero, and all others are zero

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

// N - is the number of steps in the proof
// M - the maximum length of a single step/pattern (padded with 0s if shorter)
// proof[i][j] = j-th symbol of pattern i
// annotations[i][j] = index of pattern corresponding to j-th premise of pattern i

template DotProd(M) {
    signal input a[M];
    signal input b[M];
    signal partial[M];
    signal output out;

    partial[0] <== a[0] * b[0];

    for (var i = 1; i < M; i++) {
        partial[i] <== partial[i - 1] + a[0] * b[0];
    }

    out <== partial[M - 1];
}

/* 
Validate(pattern) -> len
- computes length L of pattern
- checks that first L characters are > 0 and all others are == 0
- validates syntactical well-formedness of pattern
*/

// map the tuple t = (h, len, i) to a single field element, g(t)

template G() {
    signal input h;
    signal input len;
    signal input i;

    signal output res;
    var k = 46116860184273887237;

    res <== k * k * i + k * len + i;  
}

// add obligation of a and b
// add proof of ->a->ba

template Prop1() {
    signal input h_a;
    signal input len_a;
    signal input h_b;
    signal input len_b;
    signal input index;

    // Power annotations
    signal input r;
    signal input r_pow_len_a;
    signal input r_pow_len_b;

    signal r_pow_len_a_plus_one <== r_pow_len_a * r;
    signal r_pow_len_b_plus_one <== r_pow_len_b * r;
    
    // Obligations
    signal output o1 <== G()(h_a, len_a, 0);
    signal output o2 <== G()(h_b, len_b, 0);

    signal imp_a <== 1 + r * h_a;
    signal temp <== r_pow_len_b_plus_one * h_a;
    signal imp_ba <== 1 + r * h_b + temp;

    signal h_res <== imp_a + r_pow_len_a_plus_one * imp_ba;
    signal len_res <== 2 + 2 * len_a + len_b; 

    // Proof
    signal output p <== G()(h_res, len_res, index);
}

// add obligation of a
// add obligation of ->ab
// add proof of b

template ModusPonens() {
    signal input h_a;
    signal input len_a;
    signal input hint_a;
    signal input h_b;
    signal input len_b;
    signal input hint_ab;
    signal input index;

    // Power annotations
    signal input r;
    signal input r_pow_len_a;
    signal input r_pow_len_b;

    signal ab <== h_a + r_power_len_a * h_b;
    signal h_ab <== 1 + r * ab;
    signal len_ab <== len_a + len_b;
    
    // Obligations
    signal output o1 <== G()(h_a, len_a, hint_a);
    signal output o2 <== G()(h_ab, len_ab, hint_ab);

    // Proof
    signal output p <== G()(h_b, len_b, index);
}

template CheckProof (C, M, N) {
    signal input r;
    signal input claim[M];
    signal input commitments[C][M];
    signal input proof[N][10];
    signal input step_type[N];
    signal output out; 
    signal r_pow[M];

    // Compute first M powers of r
    r_pow[0] <== 1;
    for (var i = 1; i < M; i++) {
        r_pow[i] <== r_pow[i - 1] * r;
    }

    signal hc[C];
    signal len[C];

    // Hash the committed patterns
    for (var i = 0; i < C; i++) {
        hc[i] <== DotProd(M)(r_pow, commitments[i]);
        //len[i] <== Validate(M)(commitments[i]);
    }

    signal oblig_eval[C + 1];
    signal proof_eval[C + 1];

    oblig_eval[0] <== 1;
    proof_eval[0] <== 1;

    for (var i = 0; i < C; i++) {       
        signal oblig_coef <== 1;
        signal proof_coef <== 1;

        signal modus_ponens_res = ModusPonens()(
            proof[i][0],
            proof[i][1],
            proof[i][2],
            proof[i][3],
            proof[i][4],
            proof[i][5],
            proof[i][6],
            r,
            r, // mock
            r, // mock
        )

        oblig_eval[i] <== oblig_eval[i - 1] * oblig_coef;
        proof_eval[i] <== proof_eval[i - 1] * proof_coef;
    }
}