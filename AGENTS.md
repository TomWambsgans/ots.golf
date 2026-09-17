# ots.golf — submission rules

ots.golf is a two-track, Lean-kernel-verified competition on the worst-case verification cost of
hash-based one-time signatures. The model is `formal/OptimalOTS/Statement.lean`. Everything a
submission must satisfy is in this file; `challenges.json` is the machine-readable version, and
`verifier/` runs the same checks as the hosted verifier.

## Layout

```
formal/                      the Lean project (lake root)
  OptimalOTS/Statement.lean  the contract: Scheme, Secure, verifyCost, paperParams
  OptimalOTS/Challenge/      stubs (*.lean.in), rendered with your claim
  Submissions/Lower/         lower-track root; baseline: the paper's proof, claim 25
  Submissions/Upper/         upper-track root; baseline: a forest of 63 chains, claim 106
verifier/                    checks, contract pin, comparator configs, verify.py
challenges.json              tracks, limits, protected files
```

Protected files (listed in `challenges.json`, pinned in `verifier/protected.sha256`) always come
from the contract, never from a submission. A submission is the content of one submission root and
nothing else.

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

**Upper track** (`formal/Submissions/Upper/`, smaller is better; a record needs claim ≤ record − 1):

```lean
noncomputable def OptimalOTS.Challenge.Upper.scheme : Scheme paperParams := ...
theorem OptimalOTS.Challenge.Upper.secure : scheme.Secure := ...
theorem OptimalOTS.Challenge.Upper.cost :
    ∀ i : Fin paperParams.numSets, scheme.verifyCost i ≤ <claim> := ...
```

`scheme` is a definition hole: any term of type `Scheme paperParams` is admissible, and the two
theorems pin it down. Describe the scheme in the pull request; the leaderboard shows the
description.

## Rules for the submission root

1. **Flat.** Only `.lean` files named as identifiers, `claim.txt`, and optionally `README.md`. No
   subdirectories. `Solution.lean` is required: it is the module the verifier exports from.
2. **Imports.** Only `Mathlib`, `VCVio`, `OptimalOTS.Statement`, and sibling files of the same root
   as `Submissions.<Track>.<File>`. Nothing else: not `OptimalOTS`, not the stubs, not the other
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

`setup_tools.sh` installs comparator and lean4export (and landrun on Linux); the `lake build` line
fetches Mathlib and builds VCVio, the contract and the two baselines. `check_submission.py` runs the policy
checks: flat root, imports, sizes, claim. `verify.py` copies the trusted tree, lays your submission
root over it, attaches a fresh clone of the warm `.lake`, renders the stub, and runs comparator
under the contract's limits; on macOS it runs unsandboxed, for development only. A `verified`
result locally is what the hosted verifier will reproduce.

## Submitting

There is one way in: a pull request against the contract repository that changes only your track's
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
