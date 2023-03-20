pragma circom 2.0.3;
include "../utils/mimcsponge.circom";

// Computes MiMC([left, right])
template HashLeftRight() {
    signal input left;
    signal input right;
    signal output hash;
    component hasher = MiMCSponge(2, 220, 1);

    hasher.ins[0] <== left;
    hasher.ins[1] <== right;
    hasher.k <== 0;
    hash <== hasher.outs[0];
}

// Computes MiMC([left_child_hash, right_child_hash, node_attribute, node_threshold])
template HashNode() {
    signal input left_child_hash;
    signal input right_child_hash;
    signal input node_attribute;
    signal input node_threshold;
    signal output hash;
    component hasher = MiMCSponge(4, 220, 1);

    hasher.ins[0] <== left_child_hash;
    hasher.ins[1] <== right_child_hash;
    hasher.ins[2] <== node_attribute;
    hasher.ins[3] <== node_threshold;
    hasher.k <== 0;
    hash <== hasher.outs[0];
}

// Computes MiMC([class, location])
template HashLeaf() {
    signal input leaf_class;
    signal input leaf_location;
    signal output hash;
    component hasher = MiMCSponge(2, 220, 1);

    hasher.ins[0] <== leaf_class;
    hasher.ins[1] <== leaf_location;
    hasher.k <== 0;
    hash <== hasher.outs[0];
}
