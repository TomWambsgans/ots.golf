# RISC-V verification track

The second upper track scores a proved upper bound on the virtual cycles of **every accepting
execution**, for every public key, message, signature, and oracle-answer path. Rejecting executions
must terminate and agree with the specification; their cycle counts are unscored.

## Certificate

[`OptimalOTS.Riscv.Submission`](../formal/OptimalOTS/Riscv.lean) contains the OTS specification,
a fixed assembly image, and an input-dependent fuel bound witnessing termination. A
`Submission.Certificate C` requires:

- Perfect correctness, signing failure at most `2^-128`, public keys of 128 bits, messages of
  256 bits, signatures of at most 5504 bits, key generation of at most 1024 compressions and
  signing of at most `2^21` compressions.
- 127-bit strong security in the existing shared random-oracle experiment.
- Exact refinement of the Lean verifier by the machine's oracle computation, preserving
  queries and randomness. Faults and fuel exhaustion are excluded on every input.
- At most `C` virtual cycles on each accepting execution. The bound need not be attained.

`implemented_secure` and `implemented_admissible` transport security and admissibility to the
machine verifier. The security experiment continues to count hash compressions for all parties;
the new score also counts the verifier's ordinary instructions. No sampled benchmark is required.

## Machine and ABI

[`RiscvMachine.lean`](../formal/OptimalOTS/RiscvMachine.lean) uses the RV64IM subset provided by
[`riscv-zkvm` at `4634e41`](https://github.com/Verified-zkEVM/riscv-zkvm/tree/4634e41b229da4256e4a1f1688b94133fffa4af0).
Each ordinary instruction costs one virtual cycle. Pseudo-instructions must be expanded.
The model fixes instruction costs rather than modeling a hardware pipeline.

`ECALL` selects one of three operations using `t0` (`x5`):

| `t0` | Operation | Arguments and result | Virtual cycles |
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

## First certified submission

`formal/Submissions/RiscvUpper/` contains the checked certificate
`OptimalOTS.Challenge.RiscvUpper.certificate : submission.Certificate 229113`, exported from
`Solution.lean` with `claim.txt` at 229113. It uses only `propext`, `Classical.choice` and
`Quot.sound`; no `native_decide`, `bv_decide` or added axiom appears anywhere in the root.

The OTS retains the existing forest graph and uses a fixed disclosure layout: two subtree digests,
three group digests and 36 chain values. The chain lengths sum to 121. The executable decoder
selects distinct tuples for the `2^115` indices; the kernel checks that

```
comp 36 121 = 41695891754464226932279920354981492 ≥ 2^115.
```

`ForestAlgorithm.certificate` proves all OTS requirements and a 141-compression bound;
`Wire.certificate` transfers them to raw signature bits. The implementation, `NodeProgram.lean`,
follows the graph one node at a time, using a separate 128-byte memory slot for each value. Its
image has **114557 RV64IM instructions** and **70272 bytes of table data**, with kernel-checked
validity. The fuel witness is the instruction count: every instruction executes at most once.

### Proof structure

The certificate bundles four facts about `RiscvUpperForest.submission`:

- **Admissibility and security** are `Wire.admissible` and `Wire.secure`, inherited by
  `Submission.scheme` definitionally.
- **Exact refinement** (`Candidate.submission_implements`) states that the machine's observed
  oracle computation, `Option.map Prod.fst <$> execute 114557 (initialState image pk m bits)`,
  equals `some <$> Wire.scheme.verify pk m bits` for every public key, message and raw signature
  bit string. `VerifierProof.image_observe` proves it against the explicit forest interpreter
  `ForestVerifier.directVerify`, and `ForestVerifierProof.directVerify_eq` identifies that
  interpreter with the certified verifier. Because the result is `some` on every path, no
  execution traps or exhausts fuel, so every input terminates, including every rejection.
- **Accepting cost** (`DirectCost.execution_cost`) bounds every successful execution at the fixed
  fuel by 229113 virtual cycles: the first instruction zeroes the hash length register and an
  invariant then charges at most two cycles per instruction.

The refinement composes four verified regions of the straight-line image with continuation
lemmas that quantify over any remaining fuel:

1. `IndexExecution.indexAndChecks_continuation`: the 512-bit message-and-nonce query, the
   115-bit index range check and the exact 5504-bit length check, rejecting exactly as specified.
2. `DecoderExecution.decodePositions_continuation`: the composition unranking decoder, whose
   memory result equals `fixedPositions` (`DecodedInput`, `ExecutionContext`).
3. `ReconstructionExecution.runNodes_observe`: induction over the 2795 named nodes. Each node's
   effect (`NodeExecution.nodeEffect_eq`) equals `transitionState <$> cursorStep`, the
   specification's sequential reader with a disclosure cursor, so every hash query is issued on the
   same bit string in the same order. `NodeRefinement` and `NodeValueProof` prove the exact
   concatenation and tag layout in memory, slot isolation and pointer preservation;
   `CursorBudget` proves that the cursor consumes exactly the 5248 payload bits.
4. `DecisionProof.decision_observe`: the final 128-bit comparison with the public key and HALT.

The specification side is `ForestVerifierProof.directReconstruct_eq`, which shows that reading
disclosures sequentially agrees with the graph's offset-addressed decoding.

`Program.lean` retains the earlier fused reconstruction image and its 59393-cycle conditional
bound as a reference; it is not the certified submission.

The official verifier accepts this root through the RISC-V challenge stub; its wall time is
recorded in [the production review](production-readiness.md). The website presents the checked
claim as a separate RISC-V upper track measured in virtual cycles, with a Satoshi-attributed local
demo fixture at zero improvement. The certificate's proof also belongs in `ots.golf-submissions`.

## Attribution

The oracle syscall boundary and counted-execution approach were informed by
[Derek Sorensen's `xmss-verify-asm` at `003facc`](https://github.com/dhsorens/xmss-verify-asm/tree/003faccf2bb26f2b1a6945d4bf4b4792aae7395f).
That project proves an XMSS implementation correct for its own specification. Its benchmark's
OTS subtotal is not a universal cost theorem for this competition, and its 42 chain values plus
192-bit nonce exceed this competition's signature budget. We use the separately pinned machine
dependency and the ots.golf forest proof; no XMSS security or cost claim is imported here.

Commits based on this work credit `Derek Sorensen <d@dhsorens.com>` as co-author.
