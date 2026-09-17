# The upper-bound proof: architecture

The upper-track baseline (`formal/Submissions/Upper/`) proves, for `flatScheme : Scheme paperParams`
(41 chains of length 20 hashed directly into the root) with

```
theorem flatScheme_secure : flatScheme.Secure
theorem flatScheme_verifyCost (i) : flatScheme.verifyCost i = 109
```

(exported as `OptimalOTS.Challenge.Upper.scheme`, `secure`, `cost` in `Solution.lean`). `Scheme.Secure` demands: for every adversary `A` and every `B` with
`CostAtMost P (experiment S A) B`, `probTrue P (experiment S A) < B / 2^127`.

## Why flat

The contract charges `⌈(k + 192) / 512⌉` compressions for a hash on `k` input bits. A chain hash (128 bits)
costs one compression, a ternary grouping hash (384 bits) two, the message index two, and a single
root over all 41 chain ends (5248 bits) eleven. An exhaustive search over forests
(`tools/search_forest.py --max-levels 4 --max-branch 41 --digest-chains 3`: chains of one length under
up to four grouping levels with branching factors up to 41, optional digest chains) finds nothing
below 109 compressions, and the flat
scheme reaches it: `11` for the root, `96` chain hashes, `2` for the index. Its disclosure sets are
the position vectors `t : Fin 41 → Fin 21` with `∑ (20 - t k) = 96`, exactly `41` revealed values
(5248 bits) each, and there are `comp 41 96 = 44630212576611386423061846738781106 > 2^115` of them.
Two distinct vectors of equal sum are incomparable, which is the only property of the family the
security proof uses.

## The proof (paper Section 7.3, reorganized for formalization)

Notation: `ε = 2^-128`, `M = 2^115`, `L = 2^21`, `N = B - 831` (budget after key generation).
`ξ : G.Rec` ranges uniformly over records (sources + hash outputs); `c₀ ξ` is the cache after
key generation (keygen point `P_v ξ = (node τ_v, input_v ξ) ↦ ξ.2 v` for every hash node).

1. **Key generation** (`Keygen.lean`): running `S.keygen` under the lazy oracle from
   `∅` outputs `((pk ξ, evalRec ξ), c₀ ξ)` with probability `|Rec|⁻¹` for each `ξ`, and the
   remaining budget is `N` for every record.

2. **Identical-until-bad** (`IUB.lean`): for a cache `c` disjoint from a cache `f`,
   `E[φ | run oa from (extend c f)] ≤ E[if Hits d f then 1 else φ (x, extend d f) | run oa from c]`
   for `φ ≤ 1`.  Applied twice: stage A (`A.choose`, `f = c₀ ξ`) and stage B
   (`A.forge >>= verify`, `f = fHid i ξ` = points of hash nodes not evaluated at the signed cut).

3. **Supermartingale master lemma** (`Master.lean`): for a potential `Φ` on caches with
   `E_u Φ(c.cacheQuery q u) ≤ Φ c + κ · cost q` at fresh queries, and any continuation bound,
   `CostAtMost (oa >>= k) b → E[F | run oa from c] ≤ Φ c + κ b`.

4. **Events** (`Events.lean`): if the verifier accepts a forgery in the stage-B
   (hidden points removed) run, then the final cache `d` satisfies one of
   * `Spr d ξ`: some entry `(τ_v, u ↦ w)` with `u ≠ input_v ξ` and `trunc w = trunc (ξ.2 v)`;
   * `Hits d (fHid i ξ)`: a hidden keygen point was queried;
   * `IdxPre d_A (u₁, i)`: a pre-signing encoding entry `u ≠ u₁` has index `i`;
   * `IdxPost d' d i`: a post-signing encoding entry has index `i`.

5. **Charges** (`Potentials.lean`), per compression:
   * node-labelled query: `ε` (hidden-point hit, by resampling a hidden coordinate) + `ε` (Spr);
   * encoding query before signing: `ε` (valid-index count `/M`) + `ε` (collision pairs, scaled
     by `L/(2^256-L)`);
   * encoding query after signing: `ε` (index equals `i`).
   Total `≤ 2ε` per compression, so `Pr[forge] ≤ 2ε N = (B-831)/2^127 < B/2^127`.

6. **Signing** (`SignIdx.lean`): `Pr[u₁ fresh ∧ i ∈ V(d_A)] ≤ |V|/M` and
   `Pr[some trial lands on a collided entry] ≤ L·pairs/(2^256-L)`.

The case `B > 2^127` is trivial (`probTrue ≤ 1 < B/2^127`), so all counting invariants may
assume `N ≤ 2^127`.

## Files

See the table in `formal/Submissions/Upper/README.md`; the module names are `Submissions.Upper.<File>`.
