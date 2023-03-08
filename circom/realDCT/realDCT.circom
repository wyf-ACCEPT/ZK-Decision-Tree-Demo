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
template HashNodes() {
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

// at each level ensures attribute comparison follows properly, assuming each val/threshold is 64 bits max
// assert true [if isLess=1, input<threshold] or [if isLess=0, input>=threshold], assert fails otherwise
template ThreshComp(){
    signal input isLess;
    signal input input_val;
    signal input threshold_val;
 
    component isz = IsZero();
    component comp = LessThan(64);
    
    isLess ==> isz.in;
    comp.in[0] <== input_val;
    comp.in[1] <== threshold_val;

    1 - isz.out === comp.out;
}

// Verifies that ADT path proof is correct for given merkle root and a leaf
// pathIndices input is an array of 0/1 selectors telling whether given pathElement is on the left or right side of merkle path (1->left, 0->right)
// nodeAttributes input is an array of attributes along the hashes computed
// nodeThresholds input is an array of thresholds corresponding to the attributes (at the nodes) where the hashes are computed while computing hashes upto root
// inputAttributes is the sorted array of attributes of the input
// leaf is the class of the input as predicted by the DT

template ADTChecker(levels) {
    signal input leaf;
    signal input root;
    // signal input pathElements[levels];
    signal input pathIndices[levels];
    signal input nodeAttributes[levels];
    signal input nodeThresholds[levels];
    signal input inputAttributes[levels];
    signal input randomness;

    component isz = IsZero();
    component hasher_class;
    component hasher_root;
    component comp;
    component selectors[levels];
    component hashers[levels];
    component thresh_comp[levels];

    signal output hash_root;
    signal output hash_dt;

    //first hash class/leaf once
    selectors[0] = DualMux();
    selectors[0].in[0] <== pathElements[0]; //the adjacent class
    selectors[0].in[1] <== leaf; //the class
    selectors[0].s <== pathIndices[0];

    hasher_class = HashNodes();
    hasher_class.left_child_hash <== selectors[0].out[0];
    hasher_class.right_child_hash <== selectors[0].out[1];
    hasher_class.curr_node_val <== nodeVals[0];
    hasher_class.node_attribute <== nodeAttributes[0];
    hasher_class.node_threshold <== nodeThresholds[0]; //works

    thresh_comp[0] = ThreshComp();
    thresh_comp[0].pathIndex <== pathIndices[0]; //position of class = (1-position of class's sibling)
    thresh_comp[0].input_val <== inputAttributes[0];
    thresh_comp[0].threshold_val <== nodeThresholds[0];
    

    var i = 1;

    // builds the authenticated decision tree (ADT) from the level above leaf upto the just below root
    while (i < levels) {
        //below should hash(left_child_hash, right_child_hash, curr_node_val, node_attribute, node_threshold)
       
        if(i == 1){
            //orders left_child_val and right_child_val properly
            selectors[i] = DualMux();
            selectors[i].in[0] <== pathElements[i];
            selectors[i].in[1] <== hasher_class.hash;
            selectors[i].s <== pathIndices[i];
            hashers[i] = HashNodes();
            hashers[i].left_child_hash <== selectors[i].out[0];
            hashers[i].right_child_hash <== selectors[i].out[1];
            hashers[i].curr_node_val <== nodeVals[i];
            hashers[i].node_attribute <== nodeAttributes[i];
            hashers[i].node_threshold <== nodeThresholds[i];

        }
        else{
            //orders left_child_val and right_child_val properly
            selectors[i] = DualMux();
            selectors[i].in[0] <== pathElements[i];
            selectors[i].in[1] <== hashers[i - 1].hash;
            selectors[i].s <== pathIndices[i];
            hashers[i] = HashNodes();
            hashers[i].left_child_hash <== selectors[i].out[0];
            hashers[i].right_child_hash <== selectors[i].out[1];
            hashers[i].curr_node_val <== nodeVals[i];
            hashers[i].node_attribute <== nodeAttributes[i];
            hashers[i].node_threshold <== nodeThresholds[i];
        }
        
        //thresholdcomphere
        thresh_comp[i] = ThreshComp();
        thresh_comp[i].pathIndex <== pathIndices[i]; //position of path = (1-position of path's sibling)
        thresh_comp[i].input_val <== inputAttributes[i];
        thresh_comp[i].threshold_val <== nodeThresholds[i];

        if(i==levels-1){
            hasher_root = HashLeftRight();
            hasher_root.left <== hashers[i].hash;
            hasher_root.right <== randomness;
            hash_root <== hasher_root.hash;
            hash_dt <== hashers[i].hash;
            root === hasher_root.hash;
            
        }

        i++;
    }
        
}


component main { public [ leaf, root, inputAttributes ] } =  ADTChecker(10);
