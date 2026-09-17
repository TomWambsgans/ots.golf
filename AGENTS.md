# ots.golf — submission rules

ots.golf is a two-track, Lean-kernel-verified competition on the worst-case verification cost of
graph-based hash-based one-time signatures. A hash query on `k` input bits costs
`⌈(k + 192) / 512⌉` compressions: the 192 overhead bits stand for a 128-bit public parameter and a
64-bit tweak, so a 128-bit chain hash costs one compression and the 512-bit message index two. Everything a submission must satisfy is in this file;
`challenges.json` is the machine-readable version and `verifier/` runs the same checks the hosted
verifier runs.

## Layout

```
formal/                         the Lean project (lake root)
  OptimalOTS/Statement.lean     THE CONTRACT: the model, `Scheme`, `Secure`, `verifyCost`, `paperParams`
  OptimalOTS/Challenge/*.lean.in  challenge stubs; rendered with your claim at verification time
  Submissions/Lower/            lower-track submission root (baseline: the paper's proof, claim 25)
  Submissions/Upper/            upper-track submission root (baseline: 41 flat chains, claim 109)
verifier/                       policy checks, contract pin, comparator configs, local verifier
challenges.json                 tracks, limits, protected files
```

Protected files (listed in `challenges.json`, pinned in `verifier/protected.sha256`) are taken
from the contract, never from a submission. A submission is the content of ONE submission root and
nothing else.

## What a submission exports

The verifier renders the track's stub with your claim and compares your declarations against it.
Names and statements must match exactly; copy them from the rendered stub.

**Lower track** (`formal/Submissions/Lower/`, larger is better, record needs claim ≥ record + 1):

```lean
theorem OptimalOTS.Challenge.Lower.candidate : VerificationLowerBound paperParams <claim> := ...
```

**Upper track** (`formal/Submissions/Upper/`, smaller is better, record needs claim ≤ record − 1):

```lean
noncomputable def OptimalOTS.Challenge.Upper.scheme : Scheme paperParams := ...
theorem OptimalOTS.Challenge.Upper.secure : scheme.Secure := ...
theorem OptimalOTS.Challenge.Upper.cost :
    ∀ i : Fin paperParams.numSets, scheme.verifyCost i ≤ <claim> := ...
```

`scheme` is a definition hole: any term of type `Scheme paperParams` is admissible. The two
theorems are what pin it down. Describe the scheme in your submission's description; the
leaderboard shows it to humans.

## Rules for the submission root

1. **Flat.** Only `.lean` files (identifier names), `claim.txt`, and optionally `README.md`.
   No subdirectories. `Solution.lean` is required; it is the module the verifier exports from.
2. **Imports.** Only `Mathlib`, `VCVio` (any depth), `OptimalOTS.Statement`, and sibling files of
   the same root as `Submissions.<Track>.<File>`. Nothing else: not `OptimalOTS`, not the stubs,
   not the other track.
3. **Claim.** `claim.txt` holds one canonical non-negative integer and at most one trailing
   newline. It is rendered into the statement the kernel checks, so it cannot lie.
4. **Axioms.** The axiom closure of the exported declarations may contain only `propext`,
   `Quot.sound` and `Classical.choice`. `native_decide` adds `Lean.ofReduceBool` and is therefore
   refused; so is `sorry`.
5. **Limits.** 200 files, 8 MiB per file, 16 MiB per root. Verification: 20 minutes wall clock,
   24 GiB memory, no network, Mathlib and VCVio prebuilt. The baseline lower proof compiles in
   under two minutes on 16 cores; a `decide` over large naturals is the usual way to blow the
   budget.
6. **Toolchain.** Exactly `formal/lean-toolchain` and `formal/lake-manifest.json`. They are
   protected; a submission cannot change them.

## Check locally before submitting

```sh
verifier/setup_tools.sh                       # once: comparator + lean4export (+ landrun on Linux)
cd formal && lake exe cache get && lake build  # once: Mathlib, VCVio, the contract, the baselines
cd ..
python3 verifier/check_submission.py lower     # policy: flat root, imports, sizes, claim
python3 verifier/verify.py lower --source .    # the full pipeline on your working tree
```

`verify.py` copies the trusted tree, lays your submission root over it, attaches a fresh clone of
the warm `.lake`, renders the stub, and runs comparator under the contract's limits. On macOS it
runs unsandboxed (development only). A `verified` result locally is what the hosted verifier will
reproduce.

## Submitting

There is one way in: a pull request against the contract repository that changes only your
track's submission root. The verifier fetches the pull request's head commit, keeps only that
root, verifies it on the trusted tree, and answers on the pull request as a commit status and a
comment with a link to the submission page. Updating the pull request re-queues its new head.

Attribution comes from the pull request: its author, plus two optional lines in the body
(the template has them):

```
Assisted by: Claude Fable 5.1 max
Co-authors: alice, bob
```

The rest of the body is the public description. A verified claim that strictly beats the record
is merged, and the merge is the promotion: the submission root in the repository is always the
current record. Other verified submissions are listed by date and their pull requests closed.
