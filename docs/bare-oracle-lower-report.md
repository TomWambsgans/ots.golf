# Bare-oracle lower-bound completion report

Date: 2026-09-17. Branch: `bare-oracle`. Starting commit: `e2eaf4e`.

## Verified result

The lower submission proves, for every weakly secure scheme of the bare single-oracle model,

```lean
theorem OptimalOTS.Challenge.Lower.candidate :
    VerificationLowerBound paperParams 18
```

There is no additional condition on the scheme: no labels, tweaks, separation, collision
restriction, or uniform-record assumption. The axiom closure is exactly
`propext`, `Classical.choice`, and `Quot.sound`. No `sorry` or `native_decide` is used.

The final official verifier runs accepted both submission roots:

```text
verified: track=lower claim=18 commit=worktree in 117.5s (log: /private/var/folders/7g/qxrr2pgj40s3ykbngr10jkkr0000gn/T/ots-verify-6hfinb8t/verify.log)
verified: track=upper claim=106 commit=worktree in 165.6s (log: /private/var/folders/7g/qxrr2pgj40s3ykbngr10jkkr0000gn/T/ots-verify-_qdyv0b9/verify.log)
```

These runs were concurrent; the earlier standalone lower-18 run took 89.5 seconds.
The earlier small lower-2 certificate was also officially verified, in 53.0 seconds.

## Mathematical findings

The two proposed fresh-coordinate steps in handoff §4 are **false as stated**. They were
settled on paper before developing the replacement attack.

1. **Information bound, paper Appendix A.1.** Two hash nodes query the same public constant;
   the first is hidden and the second is the root. Every disclosure set is empty and only the
   root is reconstructed. Observing it fixes the hidden node's fresh coordinate. The proposed
   weight outside reconstruction is therefore 256 with probability one, although disclosure
   length is zero and `Bell(1)=1`. At slack one, the proposed tail bound says `1 ≤ 1/2`.
   Partitioning collisions only among reconstructed nodes misses the hidden first occurrence.
2. **Construction bound, paper Appendix A.2.** Let `Z` be a uniform bit and take
   `h=H(Z)`, `g=H(Z)`, `r=H(Y_g)`. Compare cuts `{g}` and `{Z}`.
   The proposed fresh weight of the newly checked node `g` is zero, because its dummy
   coordinate is unused. Nevertheless the proposed attempt's conditional success is one
   with probability `2^-256` and one half otherwise. Thus
   `E[-log2 p] = 1-2^-256 > 0`. This refutes the final construction inequality itself.
   A variant in which every node reaches the root has the same obstruction.

Both examples obey the graph and cut rules. They need not be secure: the proposed intermediate
lemmas were unconditional. These counterexamples do not disprove a lower bound of 24.

The detailed derivations are in
[the information analysis](bare-oracle-information-analysis.md) and
[the construction analysis](bare-oracle-construction-analysis.md).

## Replacement proof and its Lean correspondence

The paper's main theorem and §§3–6 now prove 18 by an attack using equal reconstruction patterns.

- **§3, counting.** Suppose every verification costs at most 17. The index and root consume
  at least two compressions, leaving at most 15 other reconstructed hash nodes among at most
  1023 nonroot hashes. The exact pattern count is
  `Σ(k=0..15) choose(1023,k) = 984793598840378644322567920484352 < 2^110`.
  Among `2^115` indices, at least three quarters consequently have a pattern class of size
  at least eight. Lean: `Patterns.lean`, `PatternGoods.lean`.
- **§4, cached conversion.** Reconstruct the signed disclosure and choose any algebraic record
  consistent with it and the observed hash outputs. The actual record witnesses nonemptiness.
  Induction proves that every candidate queries the exact observed inputs at the reconstructed
  nodes. Its disclosure at another index with the same pattern therefore verifies. The Lean
  conversion lemma even allows the target reconstruction set to be a subset of the observed one.
  This is an unbounded finite computation with no oracle queries; no distribution on candidates
  is asserted. Lean: `Semantics.lean`, `Encoding.lean`, `KeygenSupport.lean`,
  `Conversion.lean`.
- **§5, fresh messages and probability.** Sample the first message after key generation.
  A cache of at most `D` strings excludes the full nonce domains of at most `D` message
  prefixes. With probability at least `9/10`, the first message's domain is entirely fresh.
  On such a domain the exact signing law gives a good-class index with probability at least
  `1/2`. Honest reconstruction adds no cache entries. Sample the second message now:
  its domain is fresh and it differs from the first message with probability at least `9/10`.
  Searching `2^122` distinct nonces hits eight target indices with probability at least
  `1/9`, by `(1-p)^T ≤ 1/(1+Tp)`.
  Lean: `CacheFresh.lean`, `Index.lean`, `SignFresh.lean`, `PatternSearch.lean`,
  `PatternHelpers.lean`.
- **§6, attack assembly.** Conversion at the found index yields an accepted signature on a new
  message. The conditional bounds multiply to success at least `9/200`.
  The complete pathwise cost, including key generation, signing and final verification, is at
  most `B = 1024 + 2^20 + 2^122 + 34`.
  Exact arithmetic proves `B/2^127 < 1/25 < 9/200`, contradicting weak security.
  Lean: `CostCore.lean`, `PatternAttack.lean`, `PatternAssembly.lean`, `Solution.lean`.

This probability argument uses the actual bare-oracle cache throughout. No separated experiment
or unproved adaptive coupling is needed.

## Numerics, limitations, and the weakened claim

`tools/tune_lower_bound.py` now defaults to exact pattern arithmetic for claim 18:

```sh
python3 tools/tune_lower_bound.py --idx 1 --claims 18,19
python3 tools/tune_lower_bound.py --method entropy --s-star 5313 --idx 1 --claims 24,25 --no-search
```

The first command confirms all conservative inequalities used by the Lean certificate.
For 19, the corresponding count is
`62105400126157768832237678313804609 > 2^115`, so this counting estimate gives no positive
fraction of large classes. This is a limitation of the present proof, not an impossibility theorem.

The conditional entropy numerics still have slack for 24, even with budget 5313. They cannot
repair either false lemma. The Bell rounding was also corrected:
`Bell(22)=4506715738447323 > 2^52`, so the hypothetical 22-node Bell budget is 5310, not 5309;
23 nodes require 5313. See [the numerical investigation](bare-oracle-numerics.md).

**18 is the largest lower bound established here. Bounds 19–24, and 25, remain open in this work.**
The old labeled-model claim 25 was lowered to 18 because its independence-based proof does not
apply to the bare contract and the suggested repair fails. The theorem's quantification was not
weakened: it still covers every weakly secure scheme. `Statement.lean` and `Weak.lean` were not
edited. Only the lower baseline in `challenges.json` changed, followed by the required repin.

## Validation and local milestones

Completed checks:

- `cd formal && lake build OptimalOTS Submissions`: passed after removing obsolete labeled modules.
- `python3 verifier/pin_contract.py check`: passed, contract id
  `9564de9198acd6555659e804186120f228c838c84de0628a608ed4722fa6efce`.
- `python3 verifier/check_submission.py lower`: passed, claim 18, 19 files, 145430 bytes.
- `python3 verifier/check_submission.py upper`: passed, claim 106, 23 files, 407404 bytes.
- `python3 verifier/verify.py lower --source . --keep`: verified, output above.
- `python3 verifier/verify.py upper --source . --keep`: verified, output above.
- Axiom audit: only the three permitted axioms; the exported theorem has a checked
  `#guard_msgs` axiom declaration.
- Paper: `latexmk` completed, nine pages, no warnings or overfull boxes;
  local PDF at `/tmp/ots-bare-paper/looking-for-optimal-OTS.pdf`.
- Site figure generation: all eight generated SVGs parsed successfully.
- `git diff --check`: passed. Diff of `Submissions/Upper/`, `Statement.lean`, and
  `Weak.lean` against the handoff commit is empty.

Local milestone commits:

| Commit | Milestone |
| --- | --- |
| `03a5fe3` | Restore the officially verified elementary lower certificate at 2 |
| `ca08401` | Record both counterexamples and add bare-oracle proof components |
| `16aa966` | Prove and certify 18; replace the obsolete pipeline and update project descriptions |

A final documentation commit records both final verifier results and this report. All work
remained on `bare-oracle`; `main` and `Submissions/Upper/` were untouched. Nothing was pushed
or deployed. Parallel agents worked on disjoint mathematical, Lean, numerical, and documentation
files. The removed labeled proof remains available at `e2eaf4e`.

## Complete changed-file list

Relative to handoff commit `e2eaf4e`; `A` means added, `M` modified, and `D` removed.
The old `Cost.lean` is replaced by `CostCore.lean`. This report is also new.

```text
M	AGENTS.md
M	README.md
M	challenges.json
M	docs/AUDIT.md
A	docs/bare-oracle-construction-analysis.md
A	docs/bare-oracle-information-analysis.md
A	docs/bare-oracle-numerics.md
M	docs/bare-oracle-port.md
M	docs/lower-bound-proof.md
D	formal/Submissions/Lower/AnalysisDefs.lean
D	formal/Submissions/Lower/Assembly.lean
D	formal/Submissions/Lower/Attack.lean
D	formal/Submissions/Lower/AvgSucc.lean
A	formal/Submissions/Lower/Cache.lean
A	formal/Submissions/Lower/CacheFresh.lean
D	formal/Submissions/Lower/Cells.lean
D	formal/Submissions/Lower/Construction.lean
D	formal/Submissions/Lower/ConstructionDefs.lean
A	formal/Submissions/Lower/Conversion.lean
D	formal/Submissions/Lower/Cost.lean
A	formal/Submissions/Lower/CostCore.lean
D	formal/Submissions/Lower/Counting.lean
D	formal/Submissions/Lower/CountingFactor.lean
D	formal/Submissions/Lower/Decomp.lean
A	formal/Submissions/Lower/Elementary.lean
A	formal/Submissions/Lower/Encoding.lean
D	formal/Submissions/Lower/Entropy.lean
D	formal/Submissions/Lower/EntropyLemmas.lean
A	formal/Submissions/Lower/Expectation.lean
A	formal/Submissions/Lower/Index.lean
D	formal/Submissions/Lower/Information.lean
A	formal/Submissions/Lower/KeygenSupport.lean
D	formal/Submissions/Lower/LazyEager.lean
D	formal/Submissions/Lower/LazyEagerDefs.lean
D	formal/Submissions/Lower/Nonce.lean
D	formal/Submissions/Lower/Numerics.lean
D	formal/Submissions/Lower/NumericsDefs.lean
D	formal/Submissions/Lower/NumericsSuccess.lean
A	formal/Submissions/Lower/PatternAssembly.lean
A	formal/Submissions/Lower/PatternAttack.lean
A	formal/Submissions/Lower/PatternGoods.lean
A	formal/Submissions/Lower/PatternHelpers.lean
A	formal/Submissions/Lower/PatternSearch.lean
A	formal/Submissions/Lower/Patterns.lean
D	formal/Submissions/Lower/Product.lean
D	formal/Submissions/Lower/RankIntegral.lean
D	formal/Submissions/Lower/Ranks.lean
D	formal/Submissions/Lower/Repetition.lean
M	formal/Submissions/Lower/Semantics.lean
D	formal/Submissions/Lower/Sign.lean
A	formal/Submissions/Lower/SignFresh.lean
M	formal/Submissions/Lower/Solution.lean
D	formal/Submissions/Lower/TailBound.lean
M	formal/Submissions/Lower/claim.txt
M	llms.txt
M	paper/looking-for-optimal-OTS.tex
M	service/app/figures.py
M	service/app/templates/_how.html
M	tools/tune_lower_bound.py
M	verifier/protected.sha256
A	docs/bare-oracle-lower-report.md
```
