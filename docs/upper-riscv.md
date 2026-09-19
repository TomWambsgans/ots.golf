# RISC-V verification track

The second upper track scores a proved upper bound on the cycles of **every execution**,
accepting or rejecting, for every public key, message, signature, and oracle-answer path. Every
execution must terminate and agree with the specification.

## Certificate

[`OptimalOTS.Riscv.Submission`](../formal/OptimalOTS/Riscv.lean) contains the OTS specification,
a fixed assembly image, and an input-dependent fuel bound witnessing termination. A
`Submission.Certificate C` requires:

- Perfect correctness, deterministic verification, signing failure at most `2^-128`, public keys
  of 128 bits, messages of 256 bits, signatures of at most 5504 bits, key generation of at most
  1024 compressions and signing of at most `2^20` compressions.
- 127-bit strong security in the existing shared random-oracle experiment.
- Exact refinement of the Lean verifier by the machine's oracle computation, preserving
  queries. Faults and fuel exhaustion are excluded on every input; the machine is deterministic
  given the oracle's answers.
- At most `C` cycles on each execution, accepting or rejecting. The bound need not be attained.

Because refinement identifies the machine's oracle computation with the Lean verifier, the
admissibility and security proofs apply to the machine verifier. The security experiment counts
hash compressions for all parties; the score also counts the verifier's ordinary instructions.

## Machine and ABI

[`RiscvMachine.lean`](../formal/OptimalOTS/RiscvMachine.lean) uses the RV64IM subset provided by
[`riscv-zkvm` at `4634e41`](https://github.com/Verified-zkEVM/riscv-zkvm/tree/4634e41b229da4256e4a1f1688b94133fffa4af0).
Each ordinary instruction costs one cycle. Pseudo-instructions must be expanded.
The model fixes instruction costs rather than modeling a hardware pipeline.

`ECALL` selects one of two operations using `t0` (`x5`):

| `t0` | Operation | Arguments and result | Cycles |
|---:|---|---|---:|
| 0 | HALT | `a0` is 0 for rejection or 1 for acceptance | 1 |
| 1 | HASH | `a0`: input pointer; `a1`: bit length; `a2`: 8-byte-aligned pointer to a 32-byte buffer | `max(1, ceil(bits/512))` |

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
A signature is the 128-bit nonce followed by the payload, so the payload starts at `0x400040`.
The image contains at most 262144 instructions and 1 MiB of fixed data, loaded at `0x200000`.
Code is immutable. Parsing, arithmetic, copying and comparison run inside the machine.

## Certified submission

The reference proof, a `UpperRiscv` submission root in the submissions repository, contains the
checked certificate
`OptimalOTS.Challenge.UpperRiscv.certificate : submission.Certificate 1628`, exported from
`Solution.lean` with `claim.txt` at 1628. It uses only `propext`, `Classical.choice` and
`Quot.sound`; no `native_decide`, `bv_decide` or added axiom appears anywhere in the root.

The OTS keeps the forest graph and the fixed disclosure layout (two subtree digests, three group
digests and 36 chain values), but reads its chain positions directly from the index. The index is
the low 128 bits of `H(message ‖ nonce)`; it is **accepted** when its 32 nibbles are all at most
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
security proof of the forest ported to it (`SignIdx`, `EncCharges`, `SignRho`, `Rows`,
`RowPotential`, `Potentials`, `StageB`, `Assembly`, `Main`). The RISC-V contract itself (`OptimalOTS.Riscv.Submission`) takes any
`AlgorithmScheme paperParams` and is unchanged. `ForestAlgorithm.certificate` proves all OTS
requirements and a 186-compression bound; `Wire.certificate` transfers them to raw signature bits.

The implementation, `CompactProgram.lean`, keeps one 32-byte slot per chain, group and subtree and
hashes in place: after the index query, a straight-line sweep over the 32 nibbles accumulates
their sum, clears a flag when a nibble exceeds 14 and stores the 36 chain positions
(`Program.nibbleChecks`). Each active chain then runs as one 55-instruction block. Its 13-instruction
prologue copies the chain's disclosed word from the payload into its slot, loads the chain's
position `p`, and jumps with `AUIPC`/`JALR` to entry `p` of a table of 14 hash steps; each step
stores the level's tag and hashes the slot in place in three instructions. The tree inputs are
assembled in a 160-byte scratch buffer. The image has **2647 RV64IM instructions** and no table
data, with kernel-checked validity. The fuel witness is the instruction count.

Because `Riscv.Refines` (defined in the submission root's `Refines.lean`, not in the contract)
requires the machine's oracle computation to equal the specification's,
the machine must issue its hash queries in the specification's node order. The forest nodes are
therefore numbered chain-major (`Names.lean`): `src k` is node `43k`, and `ci k t`, `ch k t`,
`cv k t` are nodes `43k + 1 + 3t`, `43k + 2 + 3t` and `43k + 3 + 3t`; the tree nodes keep their
indices from 2709. `ForestVerifier.order` lists each chain completely before the next, so the
specification's reader visits the nodes in the order the blocks execute them, and the payload
holds chain `k`'s disclosed word at bit `128k`.

### Cycle accounting

Every ordinary instruction costs one cycle and every hash call costs `max(1, ⌈bits / 512⌉)`, so
the certificate charges each block by the instructions it executes plus one for each 512-bit
block of hash input beyond the first. All 186 hash inputs fit one block except the 912-bit root
input, which costs two. The index phase is straight-line code: 23 instructions prepare the query
(one 16-byte nonce copy and two message copies),
the HASH costs one cycle, the nibble sweep and its checks cost 238 instructions, and the two
rejection branches, each skipped, cost one cycle each around the three-instruction length check,
267 cycles in all (`IndexRefines.indexAndChecks_refines`). A chain block costs 13 cycles for its
prologue and 3 for each of its `14 - position` hash steps. The nibbles of an accepted index sum to
166, so the 36 blocks, the six setup instructions and the one-instruction epilogue cost
`7 + 36 · 13 + 3 · 166 = 973` cycles on every accepted index (`CompactLevels.chainsCost_le`). The
remaining gap between 1628 and the 186 hash compressions is the prologues, the tag stores and the
tree-input copies.

| Region | Instructions | Certified cycles |
|---|---:|---:|
| Index query, nibble checks and position stores | 273 | 267 |
| Chain setup, 36 chain blocks and epilogue | 1987 | 973 |
| Group inputs, hashes and reads | 240 | 240 |
| Subtree hashes and reads | 100 | 100 |
| Root input and 912-bit hash | 35 | 36 |
| Decision | 12 | 12 |
| Total | 2647 | 1628 |

The table follows an accepted index. Rejecting executions stop at one of the index checks or at
the final decision, and the same certified bound of 1628 covers them.

### Proof structure

The certificate bundles four facts about `RiscvUpperForest.submission`:

- **Admissibility and security** are `Wire.admissible` and `Wire.secure`, inherited by
  `Submission.scheme` definitionally.
- **Exact refinement and cycle cost** are both read off `CompactVerifier.image_refines`, which
  proves `Riscv.Refines 2647 (initialState image pk m bits) (some <$> directVerify pk m bits) 1628`.
  `Riscv.Refines fuel s q c` states that the observed oracle computation of `s` under `fuel` equals `q` and that every
  terminating execution, accepting or rejecting, costs at most `c` cycles.
  `ForestVerifierProof.directVerify_eq` identifies the explicit forest interpreter with the certified
  verifier. Because the result is `some` on every path, no execution traps or exhausts fuel, so
  every input terminates, including every rejection.

The refinement composes the straight-line image with continuation lemmas that quantify over the
remaining fuel and add the cycle costs of each block:

1. `IndexRefines.indexAndChecks_refines`: the 384-bit message-and-nonce query, the nibble
   acceptance test and the exact 5376-bit length check, rejecting exactly as specified, at 267
   cycles. `IndexChecks` proves the sweep invariant (`Swept`): after `n` steps the sum register
   holds the first `n` nibbles' sum, the flag register records whether they are all at most 14, and
   the position array holds `14 - nibble` for each processed chain; `DecodedInput` turns the final
   memory into `PositionMemory (fixedPositions index)`.
2. `CompactLevels.chains_refines`: the chain phase, matching the specification's sequential
   reader `runNodes'` over `order`. In `CompactChains`, `prefix_run` shows that a chain's nodes
   before its disclosed level are pure and end with the disclosed word; `prologue_refines` covers
   the copy, the position load and the jump, using the word alignment of the block start;
   `step_refines` and `steps_refines` issue each remaining level's hash on the same tagged 144-bit
   input as the specification; `chain_refines` joins them and `inactive_refines` covers the 27
   chains without code. `CompactLevels.chainsFrom_refines` composes the 63 chains by induction.
3. `CompactTree.groups_refines`, `CompactSubtrees.subtrees_refines` and `CompactRoot.rootDecision_refines`: the tagged
   400-bit group and subtree inputs assembled in scratch by `tripleInput_effect`, the 912-bit
   root input by `rootLin_effect`, in-place hash outputs in the 32-byte slots, and the final
   128-bit comparison with the public key (`decision_refines`) ending in HALT.

`ForestVerifierProof` proves that the cursor consumes exactly the 5248 payload bits, and
`ForestVerifierProof.directReconstruct_eq` shows that reading disclosures sequentially agrees
with the graph's offset-addressed decoding.

`SweepRefines` keeps the per-node segment framework that the tree phase uses. The earlier images
(229113 and 59393 cycles), the composition-unranking decoder (24053, 19627 and 9041 cycles) and
the level-major guarded sweeps (5513 cycles) and the 1632-cycle image for the 256-bit nonce live
in the git history.

The official verifier accepts this root through the RISC-V challenge stub. The same root is the
initial record in `ots.golf-submissions`.

## Attribution

The oracle syscall boundary and counted-execution approach were informed by
[Derek Sorensen's `xmss-verify-asm` at `003facc`](https://github.com/dhsorens/xmss-verify-asm/tree/003faccf2bb26f2b1a6945d4bf4b4792aae7395f).
That project proves an XMSS implementation correct for its own specification. Its benchmark's
OTS subtotal is not a universal cost theorem for this competition, and its 42 chain values plus
192-bit nonce exceed this competition's signature budget. We use the separately pinned machine
dependency and the ots.golf forest proof; no XMSS security or cost claim is imported here.
