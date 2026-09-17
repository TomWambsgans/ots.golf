# ots.golf — submission rules

ots.golf is a Lean-kernel-verified competition on the worst-case verification cost of hash-based
one-time signatures, with three lower-bound frameworks and one fully generic upper track. The DAG model is
`formal/OptimalOTS/Statement.lean`; `formal/OptimalOTS/Disclosure.lean` adds the partial-disclosure class.
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
  Submissions/DisclosureLower/  partial-disclosure lower-track root
  Submissions/DisclosureUpper/  legacy partial-disclosure upper reference
verifier/                    checks, contract pin, comparator configs, verify.py
challenges.json              tracks, limits, protected files
```

Protected files (listed in `challenges.json`, pinned in `verifier/protected.sha256`) always come
from the contract, never from a submission. A submission is the content of one submission root and
nothing else.

## Frameworks

The three frameworks apply to lower bounds only. A restricted lower bound does not improve a
broader class's lower record. The single upper track uses arbitrary oracle algorithms; there are no
separate DAG or partial-disclosure upper leaderboards.

- **Generic algorithms** (`formal/OptimalOTS/Algorithm.lean`): arbitrary oracle programs. The interface
  and security-preserving 106-cost adapter are foundations; generic lower and upper submissions are not
  yet admitted. Correctness and signing-availability proofs, a pinned availability threshold and the
  generic challenge remain prerequisites for admission. The 106-cost adapter is a candidate, not a record.
  `AlgorithmLower.lean` proves a generic lower theorem for every correct, weakly secure algorithm
  with signing failure at most one half; see `docs/generic-lower.md`. This foundation theorem does
  not open generic submissions or choose their final availability threshold.
- **DAG lower** (`lower`): the unrestricted DAG model, with certified lower baseline 18.
- **Partial-disclosure lower** (`disclosure-lower`): DAG schemes with certified lower baseline 80 and at most 46 distinct
  hash origins in each signature payload. A source has no hash origins; a hash has its own node as its
  sole origin; a deterministic node inherits the union of its parents' origins. The signature's origins
  are the union across all disclosed nodes. Every parent edge counts, even if its function ignores it.

The partial-disclosure class allows arbitrary fragments and deterministic encodings, including selected
Reed–Solomon symbols of a digest. Several fragments of one hash output count once; a mixture of multiple
outputs counts each. The existing 5248-bit payload budget, 256-bit nonce, 127-bit security target, DAG
disclosure cuts and forward reconstruction stay unchanged. This does not add arbitrary decoding from
subsets of encoded symbols. See `docs/partial-disclosures.md` for the definition and proof status.

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

**Partial-disclosure lower track** (`formal/Submissions/DisclosureLower/`):

```lean
theorem OptimalOTS.Challenge.DisclosureLower.candidate :
    DisclosureVerificationLowerBound paperParams 46 <claim> := ...
```

**Legacy partial-disclosure upper reference** (`formal/Submissions/DisclosureUpper/`):

```lean
noncomputable def OptimalOTS.Challenge.DisclosureUpper.scheme : Scheme paperParams := ...
theorem OptimalOTS.Challenge.DisclosureUpper.secure : scheme.Secure := ...
theorem OptimalOTS.Challenge.DisclosureUpper.cost :
    ∀ i : Fin paperParams.numSets, scheme.verifyCost i ≤ <claim> := ...
theorem OptimalOTS.Challenge.DisclosureUpper.disclosure : scheme.DisclosureBound 46 := ...
```

The partial-disclosure lower direction and record rules are the same as for the DAG lower track.
Both partial-disclosure roots may additionally import `OptimalOTS.Disclosure`. Generic upper
declarations will require `AlgorithmScheme` and proofs of admissibility, security and verification
cost; that challenge is not yet pinned or open for submission.

## Rules for the submission root

1. **Flat.** Only `.lean` files named as identifiers, `claim.txt`, and optionally `README.md`. No
   subdirectories. `Solution.lean` is required: it is the module the verifier exports from.
2. **Imports.** Only `Mathlib`, `VCVio`, `OptimalOTS.Statement`, `OptimalOTS.Disclosure` for the two
   partial-disclosure tracks, and sibling files of the same root as `Submissions.<Track>.<File>`.
   Nothing else: not `OptimalOTS`, not the stubs, not the other
   track.
3. **Claim.** `claim.txt` holds one non-negative integer without leading zeros, at most 1,000,000,
   with at most one trailing newline. It is
   rendered into the statement the kernel checks, so it cannot lie.
4. **Axioms.** The exported declarations may depend only on `propext`, `Quot.sound` and
   `Classical.choice`. `native_decide` adds `Lean.ofReduceBool` and is refused; so is `sorry`.
5. **Limits.** 200 files, 8 MiB per file, 16 MiB per root. Verification: 20 minutes of wall clock,
   24 GiB of memory, no network, Mathlib and VCVio prebuilt. The baseline proofs verify in under
   three minutes on 16 cores; a `decide` over large naturals is the usual way to blow the budget.
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

Replace `lower` by `disclosure-lower` for the other admitted lower track. The commands for `upper`
and `disclosure-upper` still verify the preserved reference certificates locally.

`setup_tools.sh` installs comparator and lean4export (and landrun on Linux); the `lake build` line
fetches Mathlib and builds VCVio, the contract and the two baselines. `check_submission.py` runs the policy
checks: flat root, imports, sizes, claim. `verify.py` copies the trusted tree, lays your submission
root over it, attaches a fresh clone of the warm `.lake`, renders the stub, and runs comparator
under the contract's limits; on macOS it runs unsandboxed, for development only. A `verified`
result locally is what the hosted verifier will reproduce.

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
