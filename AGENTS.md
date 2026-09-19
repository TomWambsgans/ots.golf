# ots.golf — submission rules

ots.golf is a Lean-kernel-verified competition on the worst-case verification cost of hash-based
one-time signatures, with three lower-bound frameworks and two upper tracks: a fully generic
compression bound and a RISC-V implementation bound in cycles. The DAG model is
`formal/OptimalOTS/Dag.lean`; `formal/OptimalOTS/WholeWords.lean` defines the whole-word class.
`challenges.json` lists the tracks, including two closed legacy upper references; `verifier/` runs
the hosted verifier's checks.

## Layout

```
formal/                      the Lean project (lake root)
  OptimalOTS/Dag.lean  the contract: Scheme, Secure, verifyCost, paperParams
  OptimalOTS/Challenge/      stubs (*.lean.in), rendered with your claim
  Submissions/<Root>/        a submission root; lives in the submissions repository, never here
verifier/                    checks, contract pin, comparator configs, verify.py
challenges.json              tracks, limits, protected files
```

Protected files (listed in `challenges.json`, pinned in `verifier/protected.sha256`) come from
the trusted contract. A submission consists of one submission root's contents. The core holds no
proofs of any track; reference proofs are ordinary submissions.

## Frameworks

All five public tracks are open.

- **Generality 1/3** (`lower-generality-1`): whole-word DAGs with a certified lower
  bound of 93. Secret sources are independent uniform 128-bit words; hashes return 256 bits.
  Each deterministic node is a fixed public 128-bit word, selects a fixed low or high half directly
  from a hash output, or concatenates an ordered list of complete earlier values. Concatenations may repeat, reorder,
  group or be empty. Disclosures reveal complete node values. This syntax and the 5248-bit payload
  budget imply at most 41 disclosed hash origins.
- **Generality 2/3** (`lower-generality-2`): fixed DAGs with arbitrary deterministic functions and disclosure
  cuts, with certified lower bound 18.
- **Generality 3/3** (`lower-generality-3`): arbitrary oracle programs, with certified lower bound 1.
  `OracleAlgorithm.lean` defines the protected interface and statement. The lower challenge fixes
  perfect correctness, deterministic verification, signing failure at most `2^-128` for every
  public-key-dependent message choice, the paper size and resource limits, and 127-bit strong
  unforgeability. The reference proof is a `LowerGenerality3` root; see `docs/lower-generality-3.md`.
- **Upper bound** (`upper-compressions`): arbitrary oracle programs, with a verified construction at
  106 compressions. The challenge fixes perfect correctness, deterministic verification, signing
  failure at most `2^-128` for every public-key-dependent message choice, the paper size and
  resource limits, and 127-bit strong unforgeability. The reference proof is a `UpperCompressions`
  root; see `docs/upper-compressions.md`.
- **RISC-V upper bound** (`upper-riscv`): an OTS meeting the Upper bound requirements, together
  with a fixed RV64IM verifier proved to compute exactly the Lean verifier's oracle computation on
  every raw input. The score is a proved bound on the cycles of every execution, accepting or
  rejecting; the reference construction costs 1628. Its proof is a `UpperRiscv` root; see
  `docs/upper-riscv.md`.

The DAG classes share the 128-bit nonce, 127-bit security target, cuts, forward reconstruction
and actual-input compression costs. See `docs/lower-generality-1.md` for the definition and proof.

The legacy `reference-generality-2` and `reference-generality-1` tracks stay registered: their reference proofs at 106
witness that secure DAG and whole-word schemes exist. Their pinned exports and local verifier
command remain available; public admission is closed.

## Oracle model

The contract has one random oracle on bit strings (`Query := Σ k, BitVec k`). Equal input strings
receive the same answer across all uses. A scheme may put a tweak in its input and pays for those bits;
the reference upper construction uses 16-bit tweaks. Hashing costs one compression per started 512-bit block, at
least one. The 384-bit message-and-nonce index costs one compression.

The verified unrestricted DAG lower bound is 18, proved for every secure scheme by counting
reconstructed hash-node sets and converting signatures between equal sets. Bounds above 18 remain
open; research notes are in `docs/research/`. Claims require Lean-kernel-checked certificates.

## What a submission exports

The verifier renders the track's stub with your claim and compares your declarations against it.
Names and statements must match exactly; copy them from the rendered stub.

**Generality 2/3 lower track** (`formal/Submissions/LowerGenerality2/`, larger is better; a record needs claim ≥ record + 1):

```lean
theorem OptimalOTS.Challenge.LowerGenerality2.candidate :
    VerificationLowerBound paperParams <claim> := ...
```

`VerificationLowerBound` quantifies over strongly `Secure` schemes, the notion every track uses. The
lower-bound attacks forge on a new message; each lower root proves in its own `WeakSecurity.lean`
that strong security implies the weak experiment it analyses, so the bounds hold for weakly secure
schemes as well.

**Legacy DAG upper reference** (`formal/Submissions/ReferenceGenerality2/`, retained for local verification):

```lean
noncomputable def OptimalOTS.Challenge.ReferenceGenerality2.scheme : Scheme paperParams := ...
theorem OptimalOTS.Challenge.ReferenceGenerality2.secure : scheme.Secure := ...
theorem OptimalOTS.Challenge.ReferenceGenerality2.cost :
    ∀ i : Fin paperParams.numSets, scheme.verifyCost i ≤ <claim> := ...
```

`scheme` is a definition hole: any term of type `Scheme paperParams` is admissible, and the two
theorems pin it down. This is the preserved DAG certificate; generic upper has its own export below.

**Generality 1/3 lower track** (`formal/Submissions/LowerGenerality1/`):

```lean
theorem OptimalOTS.Challenge.LowerGenerality1.candidate :
    WholeWordVerificationLowerBound paperParams <claim> := ...
```

**Generality 3/3 lower track** (`formal/Submissions/LowerGenerality3/`):

```lean
theorem OptimalOTS.Challenge.LowerGenerality3.candidate :
    AlgorithmVerificationLowerBound paperParams AlgorithmScheme.paperLimits (1 / 2 ^ 128) <claim> := ...
```

This theorem must cover every admissible, secure algorithm and every pathwise verification
budget. The challenge fixes signing failure at most `2^-128`, matching the upper track.
The retained proof lemma covers every failure allowance at most one half.

**Upper bound track** (`formal/Submissions/UpperCompressions/`, smaller is better):

```lean
noncomputable def OptimalOTS.Challenge.UpperCompressions.scheme : AlgorithmScheme paperParams := ...
theorem OptimalOTS.Challenge.UpperCompressions.admissible :
    scheme.Admissible AlgorithmScheme.paperLimits (1 / 2 ^ 128) := ...
theorem OptimalOTS.Challenge.UpperCompressions.secure : scheme.Secure := ...
theorem OptimalOTS.Challenge.UpperCompressions.cost : scheme.VerifyCostAtMost <claim> := ...
```

Admissibility includes perfect correctness, deterministic verification, signing failure at most
`2^-128`, an injective signature encoding of at most 5376 bits, rejection of oversized signatures,
and pathwise limits of 1024 key-generation compressions and `2^20` signing compressions.
Availability is averaged over honest key generation and signing from a fresh oracle, for every
message chosen as a function of the public key. Verification cost covers every input and
oracle-answer path, including rejection. A record needs claim ≤ record − 1.

**RISC-V upper bound track** (`formal/Submissions/UpperRiscv/`, smaller is better):

```lean
noncomputable def OptimalOTS.Challenge.UpperRiscv.submission : Riscv.Submission := ...
theorem OptimalOTS.Challenge.UpperRiscv.certificate : submission.Certificate <claim> := ...
```

`Riscv.Submission` bundles the OTS algorithms, a fixed RV64IM image and a per-input fuel witness.
The certificate proves the Upper bound admissibility and 127-bit strong security of the OTS, exact
refinement of its Lean verifier by the machine's complete oracle computation on every public key,
message and raw signature bit string, and at most `<claim>` cycles on every execution, accepting
or rejecting. Refinement excludes traps and fuel exhaustion, so every execution terminates. Each
ordinary instruction and HALT costs one cycle; HASH costs `max(1, ⌈bits / 512⌉)` on its exact
input and uses the competition's single oracle. The machine, loader and system calls are fixed in
`formal/OptimalOTS/RiscvMachine.lean`. A record needs claim ≤ record − 1.

The whole-word lower direction and record rules are the same as for the DAG lower track.

## Rules for the submission root

1. **Flat.** A single directory containing only identifier-named `.lean` files, `claim.txt`,
   and optional `NOTES.md` and `README.md`. `Solution.lean` is required: it is the module the
   verifier exports from.
2. **Imports.** Every root may import `Mathlib` and `VCVio` modules, `OptimalOTS.Dag`, and
   sibling files of the same root as `Submissions.<Root>.<File>`; all construction and proof helpers
   must be such siblings. Contract modules are exact imports, never prefixes. Additionally:

   | Root | Additional contract modules |
   |---|---|
   | `LowerGenerality2`, `ReferenceGenerality2` | none |
   | `LowerGenerality1` | `OptimalOTS.WholeWords` |
   | `LowerGenerality3`, `UpperCompressions` | `OptimalOTS.OracleAlgorithm` |
   | `UpperRiscv` | `OptimalOTS.OracleAlgorithm`, `OptimalOTS.RiscvMachine`, `OptimalOTS.Riscv` |

3. **Claim.** `claim.txt` holds one non-negative integer without leading zeros, at most 1,000,000,
   with at most one trailing newline. The verifier embeds this integer in the theorem it checks.
4. **Axioms.** The exported declarations may depend only on `propext`, `Quot.sound` and
   `Classical.choice`. `native_decide` adds `Lean.ofReduceBool` and is refused; so is `sorry`.
5. **Limits.** 200 files, 8 MiB per file, 16 MiB per root. Verification: 20 minutes of wall clock,
   24 GiB of memory, no network, Mathlib and VCVio prebuilt. Run the official verifier to measure
   a submission; a `decide` over large naturals can exceed the budget.
6. **Toolchain.** Exactly `formal/lean-toolchain` and `formal/lake-manifest.json`. Both are
   protected.

## Check locally before submitting

From the root of a submissions checkout, whose `.contract` submodule is this core:

```sh
.contract/verifier/setup_tools.sh                                        # once
(cd .contract/formal && lake exe cache get && lake build OptimalOTS)     # once
python3 .contract/verifier/verify.py lower-generality-2 --source .                    # the full pipeline
```

Replace `lower-generality-2` by `lower-generality-1` or `lower-generality-3` for the other lower tracks, or by
`upper-compressions` or `upper-riscv` for the upper tracks; `reference-generality-2` and `reference-generality-1` verify the
legacy references locally. From a core checkout, pass the submissions checkout as `--source`.

`setup_tools.sh` requires elan and installs the pinned comparator and lean4export (and landrun on
Linux); the `lake build` line fetches Mathlib and builds VCVio and the contract. `verify.py` first
runs the policy checks of `check_submission.py` (flat root, imports, sizes, claim), then copies the
trusted tree, lays your submission root over it, attaches a fresh clone of the warm `.lake`,
renders the stub, and runs comparator under the contract's limits on Linux. Linux requires the isolated, bounded work storage and sandbox
in `service/deploy/README.md`; unsupported hosts fail closed. macOS runs unsandboxed for trusted
development only: its proof result does not certify production isolation or resource enforcement.

## Submitting

The core repository is `leanEthereum/ots.golf-dev`: model, verifier and website.
Competition PRs go to `leanEthereum/ots.golf-submissions`, which holds the merged submission roots
and a `.contract` submodule pinned to the core for local checking. From that repository, run
`python3 .contract/verifier/verify.py <track> --source .` after following its setup instructions.

There is one way in: a pull request against the submissions repository that creates or changes only your
admitted track's submission root. The verifier fetches the head commit, keeps only that root, verifies it on
the trusted core checkout, and answers on the pull request with a commit status and a comment linking to the
submission page. Pushing to the pull request re-queues its new head.

Attribution comes from the pull request: its author, plus two optional lines in the body (the
template has them):

```
Assisted by: Claude Fable 5.1 max
Co-authors: alice, bob
```

The rest of the body is the public description.

Write a `NOTES.md` in the root for the next solver, human or agent: the idea, the result, what did
not work and why, and what you would try next. The verifier reads it from the checked head whatever
the verdict, and https://ots.golf/notes.md (filter with `?track=<slug>`) collects the notes of every
submission, newest first, as plain Markdown for agents.
Read the journal before starting. Non-record submissions and failed attempts are welcome for their
notes. Every checked head stays fetchable from the submissions repository as `pull/<N>/head`,
even after its fork is deleted; the submission page gives the exact `git fetch` command.

A verified claim that strictly beats the record is merged automatically in the submissions
repository, pinned to the verified head, and the merge is the promotion. If GitHub refuses the merge
(a conflict with `main`, or a newer push), the comment says why; update the pull request and its new
head is checked again. The first verified, merged submission of a track sets its first record. The
submissions repository's roots hold the merged records. Other verified submissions appear on their solver's page, and
their pull requests are closed. Submission merges never update the trusted core checkout. See `docs/repositories.md` for workspace preparation and configuration.

## Maintaining the website

Define objects by their structure, permitted operations and exact requirements. Keep prose direct,
precise and concise. Use exclusions when they state a necessary mathematical or operational constraint;
omit lists of contrasting examples and repeated caveats.

Whenever the contract or an admission status changes, update the metadata, website, rules and
documentation in the same change. Keep lower and upper admission independent. Rules
describe requirements without current scores.

Run `tools/check_repo.py` for repository checks and `service/browser_check.py` for the seeded local
preview; setup and optional formal/official checks are documented in `tools/README.md`. Production
launch requires the acceptance checks and launch gates in `service/deploy/README.md`.
