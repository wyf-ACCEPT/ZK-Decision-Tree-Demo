pragma circom 2.0.3;
// Based on "Zero-knowledge proofs for decision tree predictions and accuracy": https://dl.acm.org/doi/pdf/10.1145/3372297.3417278
// include "https://github.com/0xPARC/circom-secp256k1/blob/master/circuits/bigint.circom";

include "./hashtree.circom";
include "../utils/bitify.circom";
include "../utils/comparators.circom";
include "../utils/mux4.circom";
include "../utils/switcher.circom";


// At each level ensures attribute comparison follows properly, assuming each val/threshold is 64 bits max
// Assert true [if is_less=1, input<threshold] or [if is_less=0, input>=threshold], assert fails otherwise
template ThreshComp(features) {
    signal input is_less;
    signal input threshold_val;
    signal input feature_idx;
    signal input input_values[features];

    component num2bit = Num2Bits(4);
    component mux4 = Mux4();
    component isz = IsZero();
    component comp = LessThan(64);
    
    num2bit.in <== feature_idx;
    mux4.s <== num2bit.out;
    mux4.c <== input_values;
    comp.in[0] <== mux4.out;
    is_less ==> isz.in;
    comp.in[1] <== threshold_val;
    1 - isz.out === comp.out;
}


// Verifies that ADT path proof is correct for given merkle root and a leaf
// `path_indices` input is an array of 0/1 selectors telling whether given pathElement is on the left or right side of merkle path (1->left, 0->right)
// `node_attributes` input is an array of attributes along the hashes computed
// `node_thresholds` input is an array of thresholds corresponding to the attributes (at the nodes) where the hashes are computed while computing hashes upto root
// `input_attributes` is the sorted array of attributes of the input
// `leaf` is the class of the input as predicted by the DT
template ADTChecker(depth, features) {
    signal input leaf_class;
    signal input leaf_location;
    signal input randomness;
    signal input root;
    signal input path_element_hashes[depth];
    signal input path_indices[depth];
    signal input node_attributes[depth];
    signal input node_thresholds[depth];
    // signal input input_attributes[depth];  // TODO: Change it to input_features [Done!]
    signal input input_attributes[features];

    signal check_path[depth];

    component leaf_hasher = HashLeaf();
    component hasher_root = HashLeftRight();
    component selectors[depth];
    component hashers[depth];
    component thresh_comp[depth];

    signal output hash_root;
    var other_value;
    var check_path_last_value;

    leaf_hasher.leaf_class <== leaf_class;
    leaf_hasher.leaf_location <== leaf_location;

    // TODO: Check pathIndices and leaf_location! [done!]

    // Builds the authenticated decision tree (ADT) from the level above leaf upto the just below root
    for (var i=0; i<depth; i++) {

        // Calculate the relation between location and indices
        check_path_last_value = (i==0) ? leaf_location : check_path[i-1];
        (check_path_last_value + path_indices[i] - 2) / 2 ==> check_path[i];

        // Orders left_child_val and right_child_val properly
        other_value = (i==0) ? leaf_hasher.hash : hashers[i - 1].hash;
        selectors[i] = Switcher();
        selectors[i].L <== path_element_hashes[i];
        selectors[i].R <== other_value;
        selectors[i].sel <== path_indices[i];

        // Hash(left_child_hash, right_child_hash, node_attribute, node_threshold)
        hashers[i] = HashNode();
        hashers[i].left_child_hash <== selectors[i].outL;
        hashers[i].right_child_hash <== selectors[i].outR;
        hashers[i].node_attribute <== node_attributes[i];
        hashers[i].node_threshold <== node_thresholds[i];
        
        // Threshold checking
        thresh_comp[i] = ThreshComp(features);
        thresh_comp[i].is_less <== path_indices[i];
        thresh_comp[i].threshold_val <== node_thresholds[i];
        thresh_comp[i].feature_idx <== node_attributes[i];
        thresh_comp[i].input_values <== input_attributes;
    }

    // Path indices checking
    check_path[depth-1] === 0;

    // Root hash checking
    hasher_root.left <== hashers[depth-1].hash;
    hasher_root.right <== randomness;
    hasher_root.hash ==> hash_root;
    // root === hash_root; // TODO: add it back
}

component main { public [ leaf_class, root, input_attributes ] } = ADTChecker(5, 16);