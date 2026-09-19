# RISC-V certificate

The fixed-layout forest in `ForestAlgorithm.lean` has a complete Lean certificate for OTS
admissibility, 127-bit strong security, and verification within 141 **compressions**.
`FixedChoice.lean` and `Unrank.lean` give an executable, injective selector for its cuts.
The security and graph proofs are adapted from the checked GenericUpper forest.

`Wire.certificate` transfers the OTS proof to raw signature bits. `CompactProgram.lean` supplies
the certified 24058-instruction RV64IM image: 32-byte value slots, one hash sweep and one read
sweep per chain level, and a scratch buffer for the tree inputs. `CompactVerifier.image_refines`
proves that the image's complete oracle computation equals the certified verifier on every input
and that every accepting execution costs at most 9041 cycles: one cycle per executed
instruction, two for the 912-bit root hash, with the guarded chain sweeps and the position decoder
charged by the path actually taken (4584 and 4033 cycles on every index). `Candidate.lean` bundles these into
`machineCertificate`, and `Solution.lean` exports `OptimalOTS.Challenge.RiscvUpper.submission`
and `certificate` at the claim in `claim.txt`.

The refinement predicate `Riscv.Refines` (`Refines.lean`) pairs the observed oracle computation
with a cycle bound. `IndexRefines` covers the index query and the input checks,
`DecoderProof` the position decoder, `CompactChains` and `CompactLevels` the chain sweeps,
`CompactTree` the group, subtree, root and decision blocks, and `SweepRefines` the generic
per-node segment framework. `NodeProgram.lean` retains the earlier one-slot-per-node image and
`VerifierProof.image_observe` its refinement at 229113 cycles; `Program.lean` retains the fused
59393-cycle reference. See [the track notes](../../../docs/riscv-upper.md).
