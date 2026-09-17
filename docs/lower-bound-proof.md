# OptimalOTS: a machine-checked verification lower bound

A Lean 4 formalization, built on [VCVio](https://github.com/Verified-zkEVM/VCVio), of the lower
bound in `paper/looking-for-optimal-OTS.tex`: with a 128-bit public key, signatures of at
most 5504 bits, and roughly 127 bits of security, every graph-based hash-based one-time signature
has a signature whose verification costs at least 25 hash units.

## The statement

`formal/OptimalOTS/Statement.lean` is the complete statement, in one file and generic in the numerical
parameters. It defines the random oracle with per-block query costs, computation graphs,
disclosure sets, key generation, signing, verification, the one-signature forgery experiment,
`Scheme.Secure`, and

```lean
def VerificationLowerBound (P : Params) (c : ℕ) : Prop :=
  ∀ S : Scheme P, S.Secure → ∃ i : Fin P.numSets, c ≤ S.verifyCost i
```

together with the parameters `paperParams` of the paper. `formal/Submissions/Lower/Solution.lean` proves
`verificationLowerBound_paper : VerificationLowerBound paperParams 25`.

A better lower bound is a proof of `VerificationLowerBound paperParams c` with `c > 25`; other
parameter regimes change `P`.

## The proof

The files in `formal/Submissions/Lower/` follow the paper.

| File | Content |
|---|---|
| `Attack.lean` | the attacker |
| `Cost.lean` | the attack experiment's total query cost |
| `LazyEagerDefs.lean`, `LazyEager.lean` | the lazy random oracle equals a uniform table on the queried cells |
| `Semantics.lean` | records, oracle tables, deterministic evaluation and reconstruction |
| `AnalysisDefs.lean`, `Cells.lean` | the finite probability space of the analysis |
| `Decomp.lean` | the experiment with a fixed table is at least an explicit sum |
| `Product.lean` | splitting a uniform table into independent parts |
| `Sign.lean`, `Nonce.lean` | the index selected by signing and the rank found by the nonce search |
| `Entropy.lean`, `EntropyLemmas.lean` | conditional entropy for a uniform choice |
| `Information.lean` | Lemma 2, the information bound |
| `ConstructionDefs.lean`, `Construction.lean` | Lemma 3, the construction bound |
| `Counting.lean`, `CountingFactor.lean` | Lemma 4, the counting bound |
| `Ranks.lean`, `TailBound.lean`, `RankIntegral.lean`, `AvgSucc.lean` | the weight at each rank and the averaged construction success |
| `Repetition.lean`, `Numerics*.lean` | Appendices A and B |
| `Assembly.lean` | the success probability of the attack exceeds 11/200 |

## Building

```sh
cd formal
lake exe cache get
lake build
```

VCVio and its dependencies compile from source on the first build.
