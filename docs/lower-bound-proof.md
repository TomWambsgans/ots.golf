# The bare-oracle verification lower bound

The contract is `formal/OptimalOTS/Statement.lean`: one random oracle on bit strings, with no
labels, tweaks, separation assumptions, or restrictions on deterministic node functions beyond
parent locality. The lower track quantifies over every weakly secure scheme:

```lean
def VerificationLowerBound (P : Params) (c : ℕ) : Prop :=
  ∀ S : Scheme P, S.WeaklySecure → ∃ i : Fin P.numSets, c ≤ S.verifyCost i
```

`Submissions/Lower/Solution.lean` now proves `VerificationLowerBound paperParams 18`.
The complete theorem builds and its axiom closure contains only `propext`, `Classical.choice`,
and `Quot.sound`. The final official verifier run accepted claim 18 in 117.5 seconds. The earlier bound of 2
was officially verified before the replacement was developed.

## Proof

Assume every verification costs at most 17. The index and root each cost at least one, so the
set of reconstructed nonroot hash nodes has size at most 15. Key generation allows at most
1024 hash nodes. Consequently there are fewer than `2^110` reconstruction patterns among
`2^115` indices. At least three quarters of indices belong to classes of size at least eight.

After receiving a signature, the attacker reconstructs it and chooses any algebraic record
consistent with the disclosed values and observed hash outputs. Every such record makes the
same queries at the observed hash nodes. Its disclosure at any index with the same reconstruction
pattern therefore verifies under the actual oracle. The choice is computationally unbounded
and makes no oracle queries; no probability distribution on candidate records is assumed.

The attacker samples its first message after key generation and its second after signing and
reconstruction. A cache of at most `D` queries excludes the full nonce domains of at most `D`
message prefixes. Each uniform-message choice thus retains at least `9/10` probability mass
with a completely fresh nonce domain (and, for the second, a different message). Conditional
on freshness, the signing law is exact, giving a good signed index with probability at least
`1/2`. Searching `2^122` distinct nonces hits a class of eight indices with probability at least
`1/9`. The converted signature wins on a new message, so it wins `weakExperiment`.

Success is at least `9/200`; the total pathwise budget is
`B = 1024 + 2^21 + 2^122 + 34`, with `B/2^127 < 1/25 < 9/200`. This contradicts weak security.
All numerical comparisons in Lean use exact arithmetic. The pattern-count argument stops at
18: allowing sixteen nonroot hash nodes produces more patterns than there are indices.

## File map

| File | Role |
| --- | --- |
| `Elementary.lean` | Unconditional cost of at least two, retained from the interim certificate |
| `Semantics.lean`, `Encoding.lean` | Algebraic graph records and disclosure round trips |
| `Cache.lean`, `Expectation.lean` | Lazy bare-oracle runs and expectation identities |
| `KeygenSupport.lean` | Actual key-generation outputs satisfy the final cache's node equations |
| `Conversion.lean` | Deterministic cached conversion whenever `E_j ⊆ E_i` |
| `Patterns.lean`, `PatternGoods.lean` | Exact pattern counts and the large-class fraction |
| `CacheFresh.lean`, `PatternHelpers.lean` | Finite-cache prefix counting and probability bounds |
| `Index.lean`, `SignFresh.lean` | Signing support and its exact fresh-cache probability law |
| `PatternSearch.lean` | Nonce search, cost, correctness, and success at least `1/9` |
| `CostCore.lean`, `PatternAttack.lean` | The attack and its total pathwise query cost |
| `PatternAssembly.lean`, `Solution.lean` | Success bound, security contradiction, exported certificate |

## Why the previous entropy proof was replaced

The labeled proof's node outputs were independent. Bare nodes can repeat earlier hidden queries.
The proposed fresh-coordinate information bound with a Bell correction and the proposed
construction bound are both false; exact counterexamples are in
`bare-oracle-information-analysis.md` and `bare-oracle-construction-analysis.md`, and Appendix A
of the paper. The repeated-pattern proof bypasses those statements. It does not prove 24 or 25.
The historical labeled proof remains available in git at `e2eaf4e`.

`tools/tune_lower_bound.py` defaults to the exact pattern arithmetic at 18.
`--method entropy --s-star 5313 --claims 24,25` reproduces conditional numerical exploration;
it cannot validate the false mathematical transfer lemmas.

## Verification

```sh
cd formal && lake build OptimalOTS Submissions
cd .. && python3 verifier/pin_contract.py check
python3 verifier/check_submission.py lower
python3 verifier/verify.py lower --source .
python3 verifier/verify.py upper --source .
```
