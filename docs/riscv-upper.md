# RISC-V verification track

The second upper track scores a proved upper bound on the cycles of **every accepting
execution**, for every public key, message, signature, and oracle-answer path. Rejecting executions
must terminate and agree with the specification; their cycle counts are unscored.

## Certificate

[`OptimalOTS.Riscv.Submission`](../formal/OptimalOTS/Riscv.lean) contains the OTS specification,
a fixed assembly image, and an input-dependent fuel bound witnessing termination. A
`Submission.Certificate C` requires:

- Perfect correctness, signing failure at most `2^-128`, public keys of 128 bits, messages of
  256 bits, signatures of at most 5504 bits, key generation of at most 1024 compressions and
  signing of at most `2^20` compressions.
- 127-bit strong security in the existing shared random-oracle experiment.
- Exact refinement of the Lean verifier by the machine's oracle computation, preserving
  queries and randomness. Faults and fuel exhaustion are excluded on every input.
- At most `C` cycles on each accepting execution. The bound need not be attained.

`implemented_secure` and `implemented_admissible` transport security and admissibility to the
machine verifier. The security experiment continues to count hash compressions for all parties;
the new score also counts the verifier's ordinary instructions. No sampled benchmark is required.

## Machine and ABI

[`RiscvMachine.lean`](../formal/OptimalOTS/RiscvMachine.lean) uses the RV64IM subset provided by
[`riscv-zkvm` at `4634e41`](https://github.com/Verified-zkEVM/riscv-zkvm/tree/4634e41b229da4256e4a1f1688b94133fffa4af0).
Each ordinary instruction costs one cycle. Pseudo-instructions must be expanded.
The model fixes instruction costs rather than modeling a hardware pipeline.

`ECALL` selects one of three operations using `t0` (`x5`):

| `t0` | Operation | Arguments and result | Cycles |
|---:|---|---|---:|
| 0 | HALT | `a0` is 0 for rejection or 1 for acceptance | 1 |
| 1 | HASH | `a0`: input pointer; `a1`: bit length; `a2`: aligned 32-byte output pointer | `max(1, ceil(bits/512))` |
| 2 | RANDOM | A fresh uniform 64-bit word in `a0` | 1 |

HASH uses the same bare oracle as key generation, signing and the attacker. Bits are read least
significant first within each byte. It reads the full input before writing the 256-bit answer;
buffers may overlap. Repeated queries are charged again. HASH has no extra one-cycle dispatch fee.
Other system calls, host accelerators and invalid memory accesses trap.

The loader packs raw inputs into memory, zeroes other memory and registers, installs the fixed
code and data, and sets these registers:

| Register | Initial value |
|---|---|
| `pc` | Code at `0x1000` |
| `sp` | `0x1000000` |
| `a0` | 128-bit public key at `0x400000` |
| `a1` | 256-bit message at `0x400010` |
| `a2` | Signature at `0x400030` |
| `a3` | Signature bit length, capped at 5505 |

The first 5504 signature bits are loaded; the length sentinel distinguishes oversized inputs.
The image contains at most 262144 instructions and 1 MiB of fixed data, loaded at `0x200000`.
Code is immutable. Parsing, arithmetic, copying and comparison run inside the machine.

## Certified submission

`formal/Submissions/RiscvUpper/` contains the checked certificate
`OptimalOTS.Challenge.RiscvUpper.certificate : submission.Certificate 5513`, exported from
`Solution.lean` with `claim.txt` at 5513. It uses only `propext`, `Classical.choice` and
`Quot.sound`; no `native_decide`, `bv_decide` or added axiom appears anywhere in the root.

The OTS keeps the forest graph and the fixed disclosure layout (two subtree digests, three group
digests and 36 chain values), but reads its chain positions directly from the index. The index is
the 128-bit prefix of `H(message ‖ nonce)`; it is **accepted** when its 32 nibbles are all at most
14 and sum to `target = 166` (`Valid.lean`). Chain `k < 32` is then disclosed at position
`14 - nibble k` and chains 32 to 35 at position 14 (`FixedChoice.lean`), so every disclosure set
is a cut of the same cost and distinct indices give distinct cuts. The kernel checks that exactly

```
comp 32 166 = 42088166900081964050093337199455360 ≥ 2^115
```

indices are accepted (`Valid.card_validSet`), so signing succeeds within the `2^20` trials with
failure below `2^-128` as before.

The paper scheme of the contract accepts an index when it is below `numSets`; this root therefore
carries `GScheme.lean`, the same graph scheme with the acceptance predicate `i ∈ validSet`, and the
security proof of the forest ported to it (`SignIdx`, `EncCharges`, `Potentials`, `StageB`,
`Assembly`, `Main`). The RISC-V contract itself (`OptimalOTS.Riscv.Submission`) takes any
`AlgorithmScheme paperParams` and is unchanged. `ForestAlgorithm.certificate` proves all OTS
requirements and a 186-compression bound; `Wire.certificate` transfers them to raw signature bits.

The implementation, `CompactProgram.lean`, keeps one 32-byte slot per chain, group and subtree and
hashes in place: after the index query, a straight-line sweep over the 32 nibbles accumulates
their sum, clears a flag when a nibble exceeds 14 and stores the 36 chain positions
(`Program.nibbleChecks`); each chain level is then one guarded hash sweep over the 36 chains
followed by one guarded read sweep that copies the disclosed values for the next level, and the
tree inputs are assembled in a 160-byte scratch buffer. Its image has **9674 RV64IM instructions**
and no table data, with kernel-checked validity. The fuel witness is the instruction count.

### Cycle accounting

Every ordinary instruction costs one cycle and every hash call costs `max(1, ⌈bits / 512⌉)`, so
the certificate charges each block by the instructions it executes plus one for each 512-bit
block of hash input beyond the first. All 186 hash inputs fit one block except the 912-bit root
input, which costs two. The index phase is straight-line code: 27 instructions prepare the query,
the HASH costs one cycle, the nibble sweep and its checks cost 238 instructions, and the two
rejection branches, each skipped, cost one cycle each around the three-instruction length check,
271 cycles in all (`IndexRefines.indexAndChecks_refines`). The guarded chain sweeps are charged by
the path taken: a read costs 9 when the chain is disclosed at that level and 4 otherwise, a hash
step costs at most 9 when the chain is hashed and 3 otherwise. Because each chain is read once
and hashed `14 - position` times, and the nibbles of an accepted index sum to 166, the chain phase
costs 4854 cycles on every accepted index (`CompactCost.chainsCost_le`). The remaining gap
between 5513 and the 186 hash compressions is the per-step overhead of the chain sweeps, copying
and tagging.

| Region | Instructions | Certified cycles |
|---|---:|---:|
| Index query, nibble checks and position stores | 277 | 271 |
| Chain setup, 15 read sweeps and 14 hash sweeps | 9010 | 4854 |
| Group inputs, hashes and reads | 240 | 240 |
| Subtree hashes and reads | 100 | 100 |
| Root input and 912-bit hash | 35 | 36 |
| Decision | 12 | 12 |
| Total | 9674 | 5513 |

### Proof structure

The certificate bundles four facts about `RiscvUpperForest.submission`:

- **Admissibility and security** are `Wire.admissible` and `Wire.secure`, inherited by
  `Submission.scheme` definitionally.
- **Exact refinement and accepting cost** are both read off `CompactVerifier.image_refines`, which
  proves `Riscv.Refines 9674 (initialState image pk m bits) (some <$> directVerify pk m bits) 5513`.
  `Riscv.Refines fuel s q c` (`Refines.lean`) states that the observed oracle computation of `s`
  under `fuel` equals `q` and that every terminating execution costs at most `c` cycles.
  `ForestVerifierProof.directVerify_eq` identifies the explicit forest interpreter with the certified
  verifier. Because the result is `some` on every path, no execution traps or exhausts fuel, so
  every input terminates, including every rejection.

The refinement composes the straight-line image with continuation lemmas that quantify over the
remaining fuel and add the cycle costs of each block:

1. `IndexRefines.indexAndChecks_refines`: the 512-bit message-and-nonce query, the nibble
   acceptance test and the exact 5504-bit length check, rejecting exactly as specified, at 271
   cycles. `IndexChecks` proves the sweep invariant (`Swept`): after `n` steps the sum register
   holds the first `n` nibbles' sum, the flag register records whether they are all at most 14, and
   the position array holds `14 - nibble` for each processed chain; `DecodedInput` turns the final
   memory into `PositionMemory (fixedPositions index)`.
2. `CompactLevels.chains_refines`: the chain phase. `SweepRefines` gives a generic per-node
   segment framework (`Segment.NodeRefines`, `sweep_refines`) matching the specification's
   sequential reader `runNodes'` over `order`; `CompactChains` proves the source reads, the
   guarded chain hashes (`ch_refines`) and the guarded reads (`cv_refines`), each hash issued on
   the same tagged 144-bit input in the same order as the specification.
3. `CompactTree.groups_refines`, `subtrees_refines` and `rootDecision_refines`: the tagged
   400-bit group and subtree inputs assembled in scratch by `tripleInput_effect`, the 912-bit
   root input by `rootLin_effect`, in-place hash outputs in the 32-byte slots, and the final
   128-bit comparison with the public key (`decision_refines`) ending in HALT.

`CursorBudget` proves that the cursor consumes exactly the 5248 payload bits, and
`ForestVerifierProof.directReconstruct_eq` shows that reading disclosures sequentially agrees
with the graph's offset-addressed decoding.

`NodeProgram.lean` retains the node-level building blocks of the earlier one-slot-per-node image;
the earlier images (229113 and 59393 cycles) and the composition-unranking decoder (24053, 19627
and 9041 cycles) live in the git history.

The official verifier accepts this root through the RISC-V challenge stub; its wall time is
recorded in [the production review](production-readiness.md). The website presents the checked
claim as a separate RISC-V upper track measured in cycles, with a Satoshi-attributed local
demo fixture at zero improvement. The certificate's proof also belongs in `ots.golf-submissions`.

## Attribution

The oracle syscall boundary and counted-execution approach were informed by
[Derek Sorensen's `xmss-verify-asm` at `003facc`](https://github.com/dhsorens/xmss-verify-asm/tree/003faccf2bb26f2b1a6945d4bf4b4792aae7395f).
That project proves an XMSS implementation correct for its own specification. Its benchmark's
OTS subtotal is not a universal cost theorem for this competition, and its 42 chain values plus
192-bit nonce exceed this competition's signature budget. We use the separately pinned machine
dependency and the ots.golf forest proof; no XMSS security or cost claim is imported here.

Commits based on this work credit `Derek Sorensen <d@dhsorens.com>` as co-author.
