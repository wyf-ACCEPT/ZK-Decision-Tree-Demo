include "../circuits/utils/mimcsponge.circom";

// component main { public [xR_in] } = MiMCFeistel(10);
component main = MiMCSponge(3, 5, 7);