pragma circom 2.1.0;

template Circuit() {
    signal input a[4];
    signal input index;
    signal output b[5];

    var temp[5], i = 0;

    /*
    for (i = 0; i < 5; i += 1) {
        temp[i] = 0;
    }*/

    b <== temp;
}

component main = Circuit();