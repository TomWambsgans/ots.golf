# ots.golf — submission rules

ots.golf is a Lean-kernel-verified competition on the worst-case verification cost of hash-based
one-time signatures, with three lower-bound frameworks and two upper tracks: a fully generic
compression bound and a RISC-V implementation bound in cycles. The DAG model is
`formal/OptimalOTS/Statement.lean`; `formal/OptimalOTS/WholeWords.lean` defines the whole-word class.
Submission requirements and current admission status are below. `challenges.json` describes the
pinned certificates, including legacy upper references; `verifier/` runs the same proof checks as
the hosted verifier. Public admission follows the framework status below.

## Layout

```
formal/                      the Lean project (lake root)
  OptimalOTS/Statement.lean  the contract: Scheme, Secure, verifyCost, paperParams
  OptimalOTS/Challenge/      stubs (*.lean.in), rendered with your claim
  Submissions/Lower/         Generality 2/3 lower root; checked claim 18
  Submissions/Upper/         legacy upper reference: a forest of 63 chains, claim 106
  Submissions/DisclosureLower/  Generality 1/3 lower root; checked claim 93
  Submissions/DisclosureUpper/  legacy partial-disclosure upper reference
  Submissions/GenericLower/     Generality 3/3 lower root; checked claim 1
  Submissions/GenericUpper/     Upper bound root; verified forest, claim 106
  Submissions/RiscvUpper/       RISC-V upper bound root; verified RV64IM verifier, claim 24053
verifier/                    checks, contract pin, comparator configs, verify.py
challenges.json              tracks, limits, protected files
```

Protected files (listed in `challenges.json`, pinned in `verifier/protected.sha256`) come from
the trusted contract. A submission consists of one submission root's contents.

## Frameworks

The three public lower classes are **Generality 3/3**, **Generality 2/3** and **Generality 1/3**,
from broadest to most restricted, each with its own record. The **Upper bound** track uses
arbitrary oracle algorithms, and the **RISC-V upper bound** track scores a verified machine
implementation. Upper admission is listed in the top-level `upper_tracks` metadata, independently
of the lower frameworks. All five public tracks are open.

- **Generality 3/3** (`generic-lower`): arbitrary oracle programs, with certified lower bound 1.
  `Algorithm.lean` and `AlgorithmWeak.lean` define the protected interface. The lower challenge fixes
  perfect correctness, signing failure at most `2^-128` for every public-key-dependent message
  choice, the paper size and resource limits, and 127-bit strong unforgeability. Proofs live in
  `formal/Submissions/GenericLower/`; see `docs/generic-lower.md`.
- **Generality 2/3** (`lower`): fixed DAGs with arbitrary deterministic functions and disclosure
  cuts, with certified lower bound 18.
- **Generality 1/3** (`disclosure-lower`, retained slug): whole-word DAGs with a certified lower
  bound of 93. Secret sources are independent uniform 128-bit words; hashes return 256 bits.
  Each deterministic node selects a fixed low or high half directly from a hash output, or
  concatenates an ordered list of complete earlier values. Concatenations may repeat, reorder,
  group or be empty. Disclosures reveal complete node values. This syntax and the 5248-bit payload
  budget imply at most 41 disclosed hash origins.
- **Upper bound** (`generic-upper`): arbitrary oracle programs, with a verified construction at
  106 compressions. The challenge fixes perfect correctness, signing failure at most `2^-128`
  for every public-key-dependent message choice, the paper size and resource limits, and 127-bit
  strong unforgeability. Proofs live in `formal/Submissions/GenericUpper/`; see `docs/generic-upper.md`.
- **RISC-V upper bound** (`riscv-upper`): an OTS meeting the Upper bound requirements, together
  with a fixed RV64IM verifier proved to compute exactly the Lean verifier's oracle computation on
  every raw input. The score is a proved bound on the cycles of every accepting execution;
  the checked construction costs 24053. Proofs live in `formal/Submissions/RiscvUpper/`; see
  `docs/riscv-upper.md`.

The DAG classes share the 256-bit nonce, 127-bit security target, cuts, forward reconstruction
and actual-input compression costs. See `docs/whole-words.md` for the definition and proof.

The existing `upper` and `disclosure-upper` roots are retained as reference certificates, both at 106.
Their pinned exports and local verifier commands remain available. Public admission to these
historical roots is closed.

## Oracle model

The contract has one random oracle on bit strings (`Query := Σ k, BitVec k`). Equal input strings
receive the same answer across all uses. A scheme may put a tweak in its input and pays for those bits;
the upper baseline uses 16-bit tweaks. Hashing costs one compression per started 512-bit block, at
least one. The 512-bit message-and-nonce index costs one compression.

The verified unrestricted DAG lower bound is 18, proved for every secure scheme by counting
reconstructed hash-node sets and converting signatures between equal sets. Bounds above 18 remain
open; research notes are in `docs/bare-oracle-port.md`. Claims require Lean-kernel-checked certificates.

## What a submission exports

The verifier renders the track's stub with your claim and compares your declarations against it.
Names and statements must match exactly; copy them from the rendered stub.

**Generality 2/3 lower track** (`formal/Submissions/Lower/`, larger is better; a record needs claim ≥ record + 1):

```lean
theorem OptimalOTS.Challenge.Lower.candidate :
    VerificationLowerBound paperParams <claim> := ...
```

`VerificationLowerBound` quantifies over strongly `Secure` schemes, the notion every track uses. The
lower-bound attacks forge on a new message, so `Scheme.Secure.weaklySecure` bridges the hypothesis to
the weak experiment they analyse, and the bounds hold for weakly secure schemes as well.

**Legacy DAG upper reference** (`formal/Submissions/Upper/`, retained for local verification):

```lean
noncomputable def OptimalOTS.Challenge.Upper.scheme : Scheme paperParams := ...
theorem OptimalOTS.Challenge.Upper.secure : scheme.Secure := ...
theorem OptimalOTS.Challenge.Upper.cost :
    ∀ i : Fin paperParams.numSets, scheme.verifyCost i ≤ <claim> := ...
```

`scheme` is a definition hole: any term of type `Scheme paperParams` is admissible, and the two
theorems pin it down. This is the preserved DAG certificate; generic upper has its own export below.

**Generality 1/3 lower track** (`formal/Submissions/DisclosureLower/`):

```lean
theorem OptimalOTS.Challenge.DisclosureLower.candidate :
    WholeWordVerificationLowerBound paperParams <claim> := ...
```

**Generality 3/3 lower track** (`formal/Submissions/GenericLower/`):

```lean
theorem OptimalOTS.Challenge.GenericLower.candidate :
    AlgorithmVerificationLowerBound paperParams AlgorithmScheme.paperLimits (1 / 2 ^ 128) <claim> := ...
```

This theorem must cover every admissible, secure algorithm and every pathwise verification
budget. The challenge fixes signing failure at most `2^-128`, matching the upper track.
The retained proof lemma covers every failure allowance at most one half.

**Upper bound track** (`formal/Submissions/GenericUpper/`, smaller is better):

```lean
noncomputable def OptimalOTS.Challenge.GenericUpper.scheme : AlgorithmScheme paperParams := ...
theorem OptimalOTS.Challenge.GenericUpper.admissible :
    scheme.Admissible AlgorithmScheme.paperLimits (1 / 2 ^ 128) := ...
theorem OptimalOTS.Challenge.GenericUpper.secure : scheme.Secure := ...
theorem OptimalOTS.Challenge.GenericUpper.cost : scheme.VerifyCostAtMost <claim> := ...
```

Admissibility includes perfect correctness, signing failure at most `2^-128`, an injective signature
encoding of at most 5504 bits, rejection of oversized signatures, and pathwise limits of 1024
key-generation compressions and `2^20` signing compressions. Availability is averaged over honest
key generation and signing from a fresh oracle, for every message chosen as a function of the
public key. Verification cost covers every input
and oracle-answer path, including rejection. A record needs claim ≤ record − 1.

**RISC-V upper bound track** (`formal/Submissions/RiscvUpper/`, smaller is better):

```lean
noncomputable def OptimalOTS.Challenge.RiscvUpper.submission : Riscv.Submission := ...
theorem OptimalOTS.Challenge.RiscvUpper.certificate : submission.Certificate <claim> := ...
```

`Riscv.Submission` bundles the OTS algorithms, a fixed RV64IM image and a per-input fuel witness.
The certificate proves the Upper bound admissibility and 127-bit strong security of the OTS, exact
refinement of its Lean verifier by the machine's complete oracle computation on every public key,
message and raw signature bit string, and at most `<claim>` cycles on every accepting
execution. Refinement excludes traps and fuel exhaustion, so every execution terminates, including
rejections, which have no cycle bound. Ordinary instructions, RANDOM and HALT cost one cycle; HASH
costs `max(1, ⌈bits / 512⌉)` on its exact input and uses the competition's single oracle. The
machine, loader and system calls are fixed in `formal/OptimalOTS/RiscvMachine.lean`. A record
needs claim ≤ record − 1.

**Legacy partial-disclosure upper reference** (`formal/Submissions/DisclosureUpper/`):

```lean
noncomputable def OptimalOTS.Challenge.DisclosureUpper.scheme : Scheme paperParams := ...
theorem OptimalOTS.Challenge.DisclosureUpper.secure : scheme.Secure := ...
theorem OptimalOTS.Challenge.DisclosureUpper.cost :
    ∀ i : Fin paperParams.numSets, scheme.verifyCost i ≤ <claim> := ...
theorem OptimalOTS.Challenge.DisclosureUpper.disclosure : scheme.DisclosureBound 46 := ...
```

The whole-word lower direction and record rules are the same as for the DAG lower track.
The restricted lower root may additionally import `OptimalOTS.WholeWords` and
`OptimalOTS.Disclosure`; the legacy partial-disclosure upper root may import `OptimalOTS.Disclosure`. Generic lower may
additionally import `OptimalOTS.Algorithm` and `OptimalOTS.AlgorithmWeak`. Generic upper may
additionally import `OptimalOTS.Algorithm`; all its construction and proof helpers must be siblings
in its own submission root. RISC-V upper may additionally import `OptimalOTS.Algorithm`,
`OptimalOTS.RiscvMachine` and `OptimalOTS.Riscv`, with the same sibling rule.

## Rules for the submission root

1. **Flat.** A single directory containing only identifier-named `.lean` files, `claim.txt`,
   and optional `README.md`. `Solution.lean` is required: it is the module the verifier exports from.
2. **Imports.** Only `Mathlib`, `VCVio`, `OptimalOTS.Statement`, `OptimalOTS.Disclosure` for the two
   historically named disclosure roots, `OptimalOTS.WholeWords` for whole-word lower,
   `OptimalOTS.Algorithm` for both generic tracks and `OptimalOTS.AlgorithmWeak` for generic lower,
   `OptimalOTS.Algorithm`, `OptimalOTS.RiscvMachine` and `OptimalOTS.Riscv` for RISC-V upper,
   and sibling files of the same root as `Submissions.<Track>.<File>`.
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

```sh
verifier/setup_tools.sh                        # once
cd formal && lake exe cache get && lake build OptimalOTS Submissions  # once
cd ..
python3 verifier/check_submission.py lower     # policy checks
python3 verifier/verify.py lower --source .    # the full pipeline
```

Replace `lower` by `disclosure-lower` or `generic-lower` for the other lower tracks, or by
`generic-upper` or `riscv-upper` for the upper tracks. The commands for `upper`
and `disclosure-upper` still verify the preserved reference certificates locally.

`setup_tools.sh` requires elan and installs the pinned comparator and lean4export (and landrun on
Linux); the `lake build` line fetches Mathlib and builds VCVio, the contract and the certificates. `check_submission.py` runs the policy
checks: flat root, imports, sizes, claim. `verify.py` copies the trusted tree, lays your submission
root over it, attaches a fresh clone of the warm `.lake`, renders the stub, and runs comparator
under the contract's limits on Linux. Linux requires the isolated, bounded work storage and sandbox
in `service/deploy/README.md`; unsupported hosts fail closed. macOS runs unsandboxed for trusted
development only: its proof result does not certify production isolation or resource enforcement.

## Submitting

The core repository is `leanEthereum/ots.golf-dev`: model, verifier, website and reference certificates.
Competition PRs go to `leanEthereum/ots.golf-submissions`, which contains the five admitted roots
and a `.contract` submodule pinned to the core for local checking. From that repository, run
`python3 .contract/verifier/verify.py <track> --source .` after following its setup instructions.

There is one way in: a pull request against the submissions repository that changes only your admitted
track's submission root. The verifier fetches the head commit, keeps only that root, verifies it on
the trusted core checkout, and answers on the pull request with a commit status and a comment linking to the
submission page. Pushing to the pull request re-queues its new head.

Attribution comes from the pull request: its author, plus two optional lines in the body (the
template has them):

```
Assisted by: Claude Fable 5.1 max
Co-authors: alice, bob
```

The rest of the body is the public description. A verified claim that strictly beats the record is
merged in the submissions repository, and the merge is the promotion. Its roots hold the merged
record submissions; the core retains its reference certificates. Other verified submissions appear
on their solver's page, and their pull requests are closed. Submission merges never update the
trusted core checkout. See `docs/repositories.md` for workspace preparation and configuration.

## Maintaining the website

Define objects by their structure, permitted operations and exact requirements. Keep prose direct,
precise and concise. Use exclusions when they state a necessary mathematical or operational constraint;
omit lists of contrasting examples and repeated caveats.

Whenever a proof, certified baseline or admission status changes, update the metadata, website,
rules and documentation in the same change. Keep lower and upper admission independent. Rules
describe requirements without current scores. Commit locally and refresh localhost, preserving
the demo rows; never push or deploy unless explicitly requested.

Run `tools/check_repo.py` for repository checks and `service/browser_check.py` for the seeded local
preview; setup and optional formal/official checks are documented in `tools/README.md`. Production
launch requires the actual-host Linux isolation/resource checks and staging GitHub acceptance flow
in `service/deploy/README.md`. Record evidence and limitations in `docs/production-readiness.md`.
