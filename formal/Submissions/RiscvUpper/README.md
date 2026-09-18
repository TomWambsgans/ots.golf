# First RISC-V certificate

The fixed-layout forest in `ForestAlgorithm.lean` has a complete Lean certificate for OTS
admissibility, 127-bit strong security, and verification within 141 **compressions**.
`FixedChoice.lean` and `Unrank.lean` give an executable, injective selector for its cuts.
The security and graph proofs are adapted from the checked GenericUpper forest.

`Wire.certificate` transfers the OTS proof to raw signature bits. `NodeProgram.lean` supplies a
114557-instruction RV64IM image with kernel-checked validity. `VerifierProof.image_observe` proves
that the image's complete oracle computation equals the certified verifier on every input, so every
execution terminates, and `DirectCost.execution_cost` bounds accepting executions by 229113
virtual cycles. `Candidate.lean` bundles these into `machineCertificate`, and `Solution.lean`
exports `OptimalOTS.Challenge.RiscvUpper.submission` and `certificate` at the claim in `claim.txt`.

The refinement is composed from `IndexExecution`, `DecoderExecution`, `ReconstructionExecution`
and `DecisionProof`; the per-node memory semantics live in `NodeRefinement`, `NodeValueProof` and
`NodeExecution`. See [the track notes](../../../docs/riscv-upper.md).
