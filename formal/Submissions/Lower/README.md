# Lower bound 18 for bare single-oracle DAGs

`Solution.lean` exports `OptimalOTS.Challenge.Lower.candidate : VerificationLowerBound paperParams 18`.
It quantifies over every secure scheme of `OptimalOTS/Statement.lean`: one shared random oracle
keyed by its input bit string, arbitrary deterministic node functions, and no separation or
tagging hypothesis.

Assume every verification costs at most 17. The index and root each cost at least one, so each
index recomputes at most 15 nonroot hash nodes, and there are fewer than `2^110` such
reconstruction patterns among `2^115` indices: at least three quarters of the indices lie in
classes of size at least eight. After receiving a signature, the attacker picks any algebraic
record consistent with the disclosed values and the observed hash outputs; its disclosure at an
index with the same pattern verifies under the actual oracle. Fresh message prefixes make the
signing law exact, a search over `2^122` nonces hits a large class with probability at least
`1/9`, and the forgery succeeds with probability at least `9/200` at total cost
`1024 + 2^20 + 2^122 + 34`, contradicting 127-bit weak security.

## Files

| File | Content |
|---|---|
| `WeakSecurity.lean` | the weak experiment; strong security implies weak security |
| `Semantics.lean`, `Encoding.lean` | algebraic graph records and deterministic evaluation; disclosure round trips |
| `Cache.lean`, `Expectation.lean` | lazy bare-oracle runs; expectation identities |
| `KeygenSupport.lean` | actual key-generation outputs satisfy the final cache's node equations |
| `Conversion.lean` | moving a disclosure between indices with equal reconstruction patterns |
| `Patterns.lean`, `PatternGoods.lean` | exact pattern counts and the large-class fraction |
| `CacheFresh.lean`, `PatternHelpers.lean` | finite-cache prefix counting and probability bounds |
| `Index.lean`, `SignFresh.lean` | signing support and its exact fresh-cache probability law |
| `PatternSearch.lean` | nonce search, its cost, correctness and success at least `1/9` |
| `CostCore.lean`, `PatternAttack.lean` | the attack and its total pathwise query cost |
| `PatternAssembly.lean`, `Solution.lean` | success bound, security contradiction, exported certificate |

Build: `cd formal && lake build Submissions.Lower.Solution`.
Official verifier: `python3 verifier/verify.py lower --source .`.
The architecture is described in `docs/lower-bound-proof.md`.
