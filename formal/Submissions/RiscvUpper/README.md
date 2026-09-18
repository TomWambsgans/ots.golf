# First RISC-V candidate

The fixed-layout forest in `ForestAlgorithm.lean` has a complete Lean certificate for OTS
admissibility, 127-bit strong security, and verification within 141 **compressions**.
`FixedChoice.lean` and `Unrank.lean` give an executable, injective selector for its cuts.
The security and graph proofs are adapted from the checked GenericUpper forest.

`Wire.certificate` transfers the OTS proof to raw signature bits. `NodeProgram.lean` supplies a
114557-instruction RV64IM image with kernel-checked validity. `DirectCost.execution_cost` bounds
successful executions by 229113 virtual cycles. The loader, 36-position assembly decoder,
high-level forest interpreter and final key comparison have checked refinement proofs.

This directory is in development. It has no cycle claim or public submission export yet.
The per-node memory refinement and complete termination/equivalence proof remain to be assembled
under `OptimalOTS.Riscv`. See [the track notes](../../../docs/riscv-upper.md).
