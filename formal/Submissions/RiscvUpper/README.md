# RISC-V certificate

The nibble-layout forest in `ForestAlgorithm.lean` has a complete Lean certificate for OTS
admissibility, 127-bit strong security, and verification within 186 **compressions**. The index
(the low 128 bits of `H(message ‖ nonce)`) is accepted when its 32 nibbles are at most 14 and sum
to 166 (`Valid.lean`); chain `k < 32` is disclosed at position `14 - nibble k` and chains 32 to 35
at position 14 (`FixedChoice.lean`). `GScheme.lean` is the paper's graph scheme with this
acceptance predicate in place of `i < numSets`, and the security and graph proofs are the checked
GenericUpper forest's, ported to it.

`Wire.certificate` transfers the OTS proof to raw signature bits. `CompactProgram.lean` supplies
the certified 2647-instruction RV64IM image: a straight-line nibble sweep that checks the index and
stores the chain positions, 32-byte value slots, one block per active chain that copies its
disclosed word and jumps into a table of 14 hash steps, and a scratch buffer for the tree inputs.
The forest nodes are numbered chain-major (`Names.lean`), so the specification's reader visits
each chain completely before the next, in the order the blocks run.
`CompactVerifier.image_refines` proves that the image's complete oracle computation equals the
certified verifier on every input and that every execution, accepting or rejecting, costs at most
1628 cycles: one cycle per executed instruction, two for the 912-bit root hash, with each chain
block charged by the path actually taken (267 cycles for the index phase and 973 for the chains on
every accepted index). `Candidate.lean` bundles these into
`machineCertificate`, and `Solution.lean` exports `OptimalOTS.Challenge.RiscvUpper.submission`
and `certificate` at the claim in `claim.txt`.

The refinement predicate `Riscv.Refines` (`Refines.lean`) pairs the observed oracle computation
with a cycle bound. `IndexChecks` and `IndexRefines` cover the index query, the nibble sweep and
the input checks, `DecodedInput` and `ExecutionContext` the state they leave for reconstruction
(input buffers, chain positions, disclosure cursor), `CompactChains` and `CompactLevels` the chain
blocks and their cost, `CompactTree`, `CompactSubtrees` and `CompactRoot` the group, subtree, root
and decision blocks, `TagStore` the tweak stores shared by all hash inputs, and `SweepRefines` the
generic per-node segment framework.
See [the track notes](https://github.com/leanEthereum/ots.golf-dev/blob/main/docs/riscv-upper.md).
