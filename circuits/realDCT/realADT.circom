pragma circom 2.0.3;
// Based on "Zero-knowledge proofs for decision tree predictions and accuracy": https://dl.acm.org/doi/pdf/10.1145/3372297.3417278
// include "https://github.com/0xPARC/circom-secp256k1/blob/master/circuits/bigint.circom";
include "../utils/mimcsponge.circom";
include "../utils/comparators.circom";


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
// template HashLeaf() {

// }

// if s == 0 returns [in[0], in[1]]
// if s == 1 returns [in[1], in[0]]
template DualMux() {
    signal input in[2];
    signal input s;
    signal output out[2];

    out[0] <== (in[1] - in[0]) * s + in[0];
    out[1] <== (in[0] - in[1]) * s + in[1];
    s * (1 - s) === 0;
}

// At each level ensures attribute comparison follows properly, assuming each val/threshold is 64 bits max
// Assert true [if is_less=1, input<threshold] or [if is_less=0, input>=threshold], assert fails otherwise
template ThreshComp(){
    signal input is_less;
    signal input input_val;
    signal input threshold_val;
 
    component isz = IsZero();
    component comp = LessThan(64);
    
    is_less ==> isz.in;
    comp.in[0] <== input_val;
    comp.in[1] <== threshold_val;
    1 - isz.out === comp.out;
}


// Verifies that ADT path proof is correct for given merkle root and a leaf
// `pathIndices` input is an array of 0/1 selectors telling whether given pathElement is on the left or right side of merkle path (0->left, 1->right)
// `nodeAttributes` input is an array of attributes along the hashes computed
// `nodeThresholds` input is an array of thresholds corresponding to the attributes (at the nodes) where the hashes are computed while computing hashes upto root
// `inputAttributes` is the sorted array of attributes of the input
// `leaf` is the class of the input as predicted by the DT

template ADTChecker(levels) {
    signal input leaf;
    signal input root;
    signal input pathElementHashes[levels];
    signal input pathIndices[levels];
    signal input nodeAttributes[levels];
    signal input nodeThresholds[levels];
    signal input inputAttributes[levels];
    signal input randomness;

    component hasher_root;
    component selectors[levels];
    component hashers[levels];
    component thresh_comp[levels];

    signal output hash_root;

    var other_value;

    // Builds the authenticated decision tree (ADT) from the level above leaf upto the just below root
    for (var i=0; i<levels; i++) {

        // Orders left_child_val and right_child_val properly
        other_value = (i==0) ? leaf : hashers[i - 1].hash;
        selectors[i] = DualMux();
        selectors[i].in[0] <== pathElementHashes[i];
        selectors[i].in[1] <== other_value;
        selectors[i].s <== pathIndices[i];

        // Hash(left_child_hash, right_child_hash, node_attribute, node_threshold)
        hashers[i] = HashNode();
        hashers[i].left_child_hash <== selectors[i].out[0];
        hashers[i].right_child_hash <== selectors[i].out[1];
        hashers[i].node_attribute <== nodeAttributes[i];
        hashers[i].node_threshold <== nodeThresholds[i];
        
        // Threshold checking
        thresh_comp[i] = ThreshComp();
        thresh_comp[i].is_less <== pathIndices[i];
        thresh_comp[i].input_val <== inputAttributes[i];
        thresh_comp[i].threshold_val <== nodeThresholds[i];
    }

    // Root hash checking
    hasher_root = HashLeftRight();
    hasher_root.left <== hashers[levels-1].hash;
    hasher_root.right <== randomness;
    hash_root <== hasher_root.hash;
    root === hash_root;
}

component main { public [ leaf, root, inputAttributes ] } =  ADTChecker(10);
