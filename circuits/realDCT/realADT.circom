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


// Swap (in[0], in[1]) if swap==1
template DualMux() {
    signal input in[2];
    signal input swap;
    signal output out[2];

    out[0] <== (in[1] - in[0]) * swap + in[0];
    out[1] <== (in[0] - in[1]) * swap + in[1];
    swap * (1 - swap) === 0;
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
// `path_indices` input is an array of 0/1 selectors telling whether given pathElement is on the left or right side of merkle path (1->left, 0->right)
// `node_attributes` input is an array of attributes along the hashes computed
// `node_thresholds` input is an array of thresholds corresponding to the attributes (at the nodes) where the hashes are computed while computing hashes upto root
// `input_attributes` is the sorted array of attributes of the input
// `leaf` is the class of the input as predicted by the DT
template ADTChecker(levels) {
    signal input leaf_class;
    signal input leaf_location;
    signal input randomness;
    signal input root;
    signal input path_element_hashes[levels];
    signal input path_indices[levels];
    signal input node_attributes[levels];
    signal input node_thresholds[levels];
    signal input input_attributes[levels];

    component leaf_hasher = HashLeaf();
    component hasher_root = HashLeftRight();
    component selectors[levels];
    component hashers[levels];
    component thresh_comp[levels];

    signal output hash_root;
    var other_value;

    leaf_hasher.leaf_class <== leaf_class;
    leaf_hasher.leaf_location <== leaf_location;

    // TODO: Check pathIndices and leaf_location!

    // Builds the authenticated decision tree (ADT) from the level above leaf upto the just below root
    for (var i=0; i<levels; i++) {

        // Orders left_child_val and right_child_val properly
        selectors[i] = DualMux();
        other_value = (i==0) ? leaf_hasher.hash : hashers[i - 1].hash;
        selectors[i].in[0] <== path_element_hashes[i];
        selectors[i].in[1] <== other_value;
        selectors[i].swap <== path_indices[i];

        // Hash(left_child_hash, right_child_hash, node_attribute, node_threshold)
        hashers[i] = HashNode();
        hashers[i].left_child_hash <== selectors[i].out[0];
        hashers[i].right_child_hash <== selectors[i].out[1];
        hashers[i].node_attribute <== node_attributes[i];
        hashers[i].node_threshold <== node_thresholds[i];
        
        // Threshold checking
        thresh_comp[i] = ThreshComp();
        log(node_thresholds[i], path_indices[i]);
        thresh_comp[i].is_less <== path_indices[i];
        thresh_comp[i].input_val <== input_attributes[i];
        thresh_comp[i].threshold_val <== node_thresholds[i];
    }

    // Root hash checking
    hasher_root.left <== hashers[levels-1].hash;
    hasher_root.right <== randomness;
    hasher_root.hash ==> hash_root;
    // root === hash_root; // TODO: add it back
}

component main { public [ leaf_class, root, input_attributes ] } = ADTChecker(5);
