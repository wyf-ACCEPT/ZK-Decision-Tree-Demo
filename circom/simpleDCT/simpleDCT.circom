pragma circom 2.1.2;

include "../utils/comparators.circom";
include "../utils/switcher.circom";

template SimpleDCT() {
    signal input x[4];
    signal output y;
    signal out;

    component ge = GreaterThan(200);

    ge.in[0] <== x[3];
    ge.in[1] <== 8;
    ge.out ==> out;

    component switcher = Switcher();

    switcher.sel <== out;
    switcher.L <== 1;
    switcher.R <== 0;
    switcher.outL ==> y;
}

component main = SimpleDCT();
