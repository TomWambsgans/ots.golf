# First RISC-V candidate

The fixed-layout forest in `ForestAlgorithm.lean` has a complete Lean certificate for OTS
admissibility, 127-bit strong security, and verification within 141 **compressions**.
`FixedChoice.lean` and `Unrank.lean` give an executable, injective selector for its cuts.
The security and graph proofs are adapted from the checked GenericUpper forest.

`Wire.certificate` transfers the OTS proof to raw signature bits. `Program.lean` supplies a
29697-instruction RV64IM image with kernel-checked validity. `MachineCost.lean` supplies the
general cost rule.

This directory is in development. It has no cycle claim or public submission export yet.
Exact oracle-program refinement and the program's accepting-cycle bound remain to be proved
under `OptimalOTS.Riscv`. See [the track notes](../../../docs/riscv-upper.md).
