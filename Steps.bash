## 1. Write *.circom and compile
circom <name>.circom --r1cs --wasm --sym --c

## 2. Give input.json and computing
node generate_witness.js <name>.wasm input.json witness.wtns

## a. Print related information
snarkjs ri <name>.r1cs                  # r1cs info
snarkjs rp <name>.r1cs <name>.sym       # r1cs print
snarkjs rej <name>.r1cs <name>.json     # r1cs export json

## b. Continuous commands
circom realADT.circom --r1cs --wasm --sym; cd realADT_js; node generate_witness.js realADT.wasm ../input.json witness.wtns; cd ..


## 3. Proving circuits with ZK: see https://docs.circom.io/getting-started/proving-circuits/

# a classic pipeline:
snarkjs powersoftau new bn128 12 pot12_0000.ptau -v
snarkjs powersoftau contribute pot12_0000.ptau pot12_0001.ptau --name="First contribution" -v
snarkjs powersoftau prepare phase2 pot12_0001.ptau pot12_final.ptau -v
snarkjs groth16 setup multiplier2.r1cs pot12_final.ptau multiplier2_0000.zkey
snarkjs zkey contribute multiplier2_0000.zkey multiplier2_0001.zkey --name="1st Contributor Name" -v
snarkjs zkey export verificationkey multiplier2_0001.zkey verification_key.json
snarkjs groth16 prove multiplier2_0001.zkey witness.wtns proof.json public.json


# 4. A specific pipeline: 

# 4.1 trusted setup
POWER=10; CIRCOM="realADT"
mkdir trusted-setup; cd trusted-setup
snarkjs powersoftau new bn128 $POWER pot${POWER}_00.ptau -v
snarkjs powersoftau contribute pot${POWER}_00.ptau pot${POWER}_01.ptau -v
snarkjs powersoftau prepare phase2 pot${POWER}_01.ptau pot${POWER}_02.ptau -v
cd ..

# 4.2 compile the circom
circom ${CIRCOM}.circom --r1cs --wasm --sym
cd trusted-setup
snarkjs groth16 setup ../${CIRCOM}.r1cs pot${POWER}_02.ptau ${CIRCOM}_00.zkey
snarkjs zkey contribute ${CIRCOM}_00.zkey ${CIRCOM}_01.zkey -v
snarkjs zkey export verificationkey ${CIRCOM}_01.zkey verification_key.json
cd ..

# 4.3 compute the witness
echo "Computing the witness.."
cd ${CIRCOM}_js; node generate_witness.js ${CIRCOM}.wasm ../input.json witness.wtns; cd ..
cd trusted-setup; snarkjs groth16 prove ${CIRCOM}_01.zkey ../${CIRCOM}_js/witness.wtns proof.json public.json; cd ..
echo "Finished."
