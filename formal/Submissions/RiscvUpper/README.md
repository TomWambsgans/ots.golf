# RISC-V certificate

The nibble-layout forest in `ForestAlgorithm.lean` has a complete Lean certificate for OTS
admissibility, 127-bit strong security, and verification within 186 **compressions**. The index
(the 128-bit prefix of `H(message ‖ nonce)`) is accepted when its 32 nibbles are at most 14 and sum
to 166 (`Valid.lean`); chain `k < 32` is disclosed at position `14 - nibble k` and chains 32 to 35
at position 14 (`FixedChoice.lean`). `GScheme.lean` is the paper's graph scheme with this
acceptance predicate in place of `i < numSets`, and the security and graph proofs are the checked
GenericUpper forest's, ported to it.

`Wire.certificate` transfers the OTS proof to raw signature bits. `CompactProgram.lean` supplies
the certified 9674-instruction RV64IM image: a straight-line nibble sweep that checks the index and
stores the chain positions, 32-byte value slots, one hash sweep and one read sweep per chain level,
and a scratch buffer for the tree inputs. `CompactVerifier.image_refines` proves that the image's
complete oracle computation equals the certified verifier on every input and that every accepting
execution costs at most 5513 cycles: one cycle per executed instruction, two for the 912-bit root
hash, with the guarded chain sweeps charged by the path actually taken (271 cycles for the index
phase and 4854 for the chains on every accepted index). `Candidate.lean` bundles these into
`machineCertificate`, and `Solution.lean` exports `OptimalOTS.Challenge.RiscvUpper.submission`
and `certificate` at the claim in `claim.txt`.

The refinement predicate `Riscv.Refines` (`Refines.lean`) pairs the observed oracle computation
with a cycle bound. `IndexChecks` and `IndexRefines` cover the index query, the nibble sweep and
the input checks, `CompactChains` and `CompactLevels` the chain sweeps, `CompactTree` the group,
subtree, root and decision blocks, and `SweepRefines` the generic per-node segment framework.
`NodeProgram.lean` retains the node-level building blocks of the earlier one-slot-per-node image.
See [the track notes](../../../docs/riscv-upper.md).
