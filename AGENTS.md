# ots.golf — submission rules

ots.golf is a Lean-kernel-verified competition on the worst-case verification cost of hash-based
one-time signatures, with three lower-bound frameworks and one fully generic upper track. The DAG model is
`formal/OptimalOTS/Statement.lean`; `formal/OptimalOTS/WholeWords.lean` defines the whole-word class.
Submission requirements and current admission status are below. `challenges.json` describes the
pinned certificates, including legacy upper references; `verifier/` runs the same proof checks as
the hosted verifier. Public admission follows the framework status below.

## Layout

```
formal/                      the Lean project (lake root)
  OptimalOTS/Statement.lean  the contract: Scheme, Secure, verifyCost, paperParams
  OptimalOTS/Challenge/      stubs (*.lean.in), rendered with your claim
  Submissions/Lower/         lower-track root; baseline: repeated reconstruction patterns, claim 18
  Submissions/Upper/         legacy upper reference: a forest of 63 chains, claim 106
  Submissions/DisclosureLower/  whole-word lower-track root
  Submissions/DisclosureUpper/  legacy partial-disclosure upper reference
  Submissions/GenericLower/     generic lower-track root; baseline claim 1
verifier/                    checks, contract pin, comparator configs, verify.py
challenges.json              tracks, limits, protected files
```

Protected files (listed in `challenges.json`, pinned in `verifier/protected.sha256`) always come
from the contract, never from a submission. A submission is the content of one submission root and
nothing else.

## Frameworks

The three frameworks apply to lower bounds only. A restricted lower bound does not improve a
broader class's lower record. The single upper track uses arbitrary oracle algorithms; there are no
separate DAG or whole-word upper leaderboards.

- **Generic lower** (`generic-lower`): arbitrary oracle programs, with certified baseline 1.
  `Algorithm.lean` and `AlgorithmWeak.lean` define the protected interface. The lower challenge fixes
  perfect correctness, signing failure at most one half for every public-key-dependent message
  choice, the paper size and resource limits, and 127-bit weak unforgeability. Proofs live in
  `formal/Submissions/GenericLower/`; see `docs/generic-lower.md`.
- **Generic upper** remains in preparation. The security-preserving 106-cost adapter is a candidate,
  not an admitted record. Its correctness and signing-availability proofs and the upper challenge
  remain prerequisites for admission. This does not block generic lower submissions.
- **DAG lower** (`lower`): the unrestricted DAG model, with certified lower baseline 18.
- **Whole-word lower** (`disclosure-lower`, retained slug): DAG schemes with a certified lower
  bound of 93. Secret sources are 128 bits. Hash outputs are 256 bits, with either fixed 128-bit
  half available. The only other deterministic operation is concatenation, with any number of
  earlier words, including repetition and reordering. Grouping whole words into longer values is
  permitted; disclosures reveal complete node values. There are no other deterministic functions
  or nonempty constant nodes. The syntax itself implies at most 41 disclosed hash origins from
  the 5248-bit payload budget; this is a proved consequence, not an additional admission condition.

The 256-bit nonce, 127-bit security target, DAG cuts, forward reconstruction and actual-input
compression costs are unchanged. Frameworks 1 and 2 retain their existing contracts. Arbitrary
bit fragments and Reed–Solomon transformations remain available in the unrestricted DAG class,
not in whole words. See `docs/whole-words.md` for the definition and proof.

The existing `upper` and `disclosure-upper` roots are retained as reference certificates, both at 106.
Their pinned exports and local verifier commands remain available. The website rejects new submissions
to these legacy upper roots; their historical rows are not generic upper records.

## Oracle model

The contract has one random oracle on bit strings (`Query := Σ k, BitVec k`). There are no labels,
tweaks or separation conditions in the model. Equal input strings receive the same answer, including
when a node query equals an index query. A scheme may put a tweak in its input and pays for those bits;
the upper baseline uses 16-bit tweaks. Hashing costs one compression per started 512-bit block, at
least one. The 512-bit message-and-nonce index costs one compression.

The verified unrestricted DAG lower bound is 18, proved for every weakly secure scheme by counting
reconstructed hash-node sets and converting signatures between equal sets. Bounds above 18 remain
open; research notes are in `docs/bare-oracle-port.md`. A numerical search is not a certificate.

## What a submission exports

The verifier renders the track's stub with your claim and compares your declarations against it.
Names and statements must match exactly; copy them from the rendered stub.

**Lower track** (`formal/Submissions/Lower/`, larger is better; a record needs claim ≥ record + 1):

```lean
theorem OptimalOTS.Challenge.Lower.candidate :
    VerificationLowerBound paperParams <claim> := ...
```

`VerificationLowerBound` quantifies over `WeaklySecure` schemes (forgeries on a new message only),
a larger class than the `Secure` schemes of the upper track, so a lower bound also covers malleable
schemes. The attacker of a lower-bound proof must therefore forge on a message other than the signed one.

**Legacy DAG upper reference** (`formal/Submissions/Upper/`, retained for local verification):

```lean
noncomputable def OptimalOTS.Challenge.Upper.scheme : Scheme paperParams := ...
theorem OptimalOTS.Challenge.Upper.secure : scheme.Secure := ...
theorem OptimalOTS.Challenge.Upper.cost :
    ∀ i : Fin paperParams.numSets, scheme.verifyCost i ≤ <claim> := ...
```

`scheme` is a definition hole: any term of type `Scheme paperParams` is admissible, and the two
theorems pin it down. This is the preserved DAG certificate, not the future generic upper export.

**Whole-word lower track** (`formal/Submissions/DisclosureLower/`):

```lean
theorem OptimalOTS.Challenge.DisclosureLower.candidate :
    WholeWordVerificationLowerBound paperParams <claim> := ...
```

**Generic lower track** (`formal/Submissions/GenericLower/`):

```lean
theorem OptimalOTS.Challenge.GenericLower.candidate :
    AlgorithmVerificationLowerBound paperParams AlgorithmScheme.paperLimits (1 / 2) <claim> := ...
```

This theorem must cover every admissible, weakly secure algorithm and every pathwise verification
budget. The one-half signing-failure allowance is fixed by the challenge; a submission cannot
narrow the class to obtain a larger bound. It also covers every stricter availability allowance.

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
additionally import `OptimalOTS.Algorithm` and `OptimalOTS.AlgorithmWeak`. Generic upper
declarations will require `AlgorithmScheme` and proofs of admissibility, security and verification
cost; that challenge is not yet pinned or open for submission.

## Rules for the submission root

1. **Flat.** Only `.lean` files named as identifiers, `claim.txt`, and optionally `README.md`. No
   subdirectories. `Solution.lean` is required: it is the module the verifier exports from.
2. **Imports.** Only `Mathlib`, `VCVio`, `OptimalOTS.Statement`, `OptimalOTS.Disclosure` for the two
   historically named disclosure roots, `OptimalOTS.WholeWords` for whole-word lower,
   `OptimalOTS.Algorithm` and `OptimalOTS.AlgorithmWeak` for generic lower,
   and sibling files of the same root as `Submissions.<Track>.<File>`.
   Nothing else: not `OptimalOTS`, not the stubs, not the other
   track.
3. **Claim.** `claim.txt` holds one non-negative integer without leading zeros, at most 1,000,000,
   with at most one trailing newline. It is
   rendered into the statement the kernel checks, so it cannot lie.
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

Replace `lower` by `disclosure-lower` or `generic-lower` for the other lower tracks. The commands for `upper`
and `disclosure-upper` still verify the preserved reference certificates locally.

`setup_tools.sh` requires elan and installs the pinned comparator and lean4export (and landrun on
Linux); the `lake build` line fetches Mathlib and builds VCVio, the contract and the certificates. `check_submission.py` runs the policy
checks: flat root, imports, sizes, claim. `verify.py` copies the trusted tree, lays your submission
root over it, attaches a fresh clone of the warm `.lake`, renders the stub, and runs comparator
under the contract's limits on Linux. Linux requires the isolated, bounded work storage and sandbox
in `service/deploy/README.md`; unsupported hosts fail closed. macOS runs unsandboxed for trusted
development only: its proof result does not certify production isolation or resource enforcement.

## Submitting

There is one way in: a pull request against the contract repository that changes only your admitted track's
submission root. The verifier fetches the head commit, keeps only that root, verifies it on the
trusted tree, and answers on the pull request with a commit status and a comment linking to the
submission page. Pushing to the pull request re-queues its new head.

Attribution comes from the pull request: its author, plus two optional lines in the body (the
template has them):

```
Assisted by: Claude Fable 5.1 max
Co-authors: alice, bob
```

The rest of the body is the public description. A verified claim that strictly beats the record is
merged, and the merge is the promotion: the submission root in the repository is always the current
record. Other verified submissions appear on their solver's page, and their pull requests are closed.

## Maintaining the website

Whenever a proof, certified baseline or admission status changes, update the metadata, website,
rules and documentation in the same change. Keep lower and upper admission independent. Rules
describe requirements without current scores. Commit locally and refresh localhost, preserving
the demo rows; never push or deploy unless explicitly requested.

Run `tools/check_repo.py` for repository checks and `service/browser_check.py` for the seeded local
preview; setup and optional formal/official checks are documented in `tools/README.md`. Production
launch requires the actual-host Linux isolation/resource checks and staging GitHub acceptance flow
in `service/deploy/README.md`. Record evidence and limitations in `docs/production-readiness.md`.
