pragma circom 2.1.0;

template Circuit() {
    signal input a[4];
    signal output out;

    var temp[5], i = 0;

    // a[0] * a[0]
    //var x = a[0] * a[0] + a[1] * a[1] + a[2] * a[2];
    var x = (a[0] + a[1]) * (a[2] + a[3]);

    out <== x;
}

component main = Circuit();