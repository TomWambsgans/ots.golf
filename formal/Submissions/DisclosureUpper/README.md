# Partial-disclosure upper baseline: the forest scheme, 106 compressions

The scheme of Section 7 of the paper: 63 hash chains of length 14 whose ends are grouped three by
three into 21 group digests, grouped three by three into 7 subtree digests, hashed together into
the root. The contract has one random oracle and no domain separation, so the scheme separates its
hash nodes itself: every hash input starts with a 16-bit tweak naming its node (`tw`, in `Names.lean`).
A chain step hashes 144 bits, a grouping hash 400, the root 912, and none of them has the 384 bits of
an index query. Chain and grouping hashes still cost one compression, the root two. A signature reveals one 128-bit
value on every source-to-root path, and the `2 ^ 115` disclosure sets are cuts of reconstruction
cost 105 with at most 41 revealed values (so at most 5248 revealed bits): every signature verifies
in `1 + 105 = 106` compressions, and the scheme meets the 127-bit strong-unforgeability requirement of
`OptimalOTS/Statement.lean`. The proof gives `Pr[forge] ≤ (B - 912) / 2 ^ 127` for every budget
`B ≤ 2 ^ 127`.

Every disclosed value is a secret source or the 128-bit truncation of a single hash output.
`Origins.lean` proves that the union of the payload's underlying hash outputs has cardinality
at most 41, establishing the framework's limit of 46 without changing the construction or its
security experiment.

Exports (`Solution.lean`): `OptimalOTS.Challenge.DisclosureUpper.scheme`, `secure`, `cost`, and
`disclosure : scheme.DisclosureBound 46`.

## Files

| File | Content |
|---|---|
| `Semantics.lean` | records, deterministic evaluation, reconstruction with oracle tables (shared with the lower track; copied, since submissions cannot import each other) |
| `Cache.lean`, `IUB.lean`, `Master.lean` | the lazy random oracle's cache; the identical-until-bad coupling; the supermartingale master lemma (a potential growing by at most `κ` per compression bounds a bad event by `κ · budget`) |
| `Keygen.lean`, `Reconstruct.lean`, `SignIdx.lean`, `EncCharges.lean` | key generation as a uniform record; the verifier's run; the signing loop; charges of encoding queries |
| `Names.lean`, `Tree.lean` | the 2795-node computation graph; the tree structure, visited sets, costs, cuts |
| `Count.lean`, `Cuts.lean`, `Scheme.lean` | the disclosure family (more than `2 ^ 115` sets, certified by kernel computation) and `forestScheme` |
| `Origins.lean` | each disclosed value has at most one hash origin; the whole payload has at most 41 |
| `Values.lean`, `Resample.lean`, `Events.lean` | node values; hidden and exposed keygen points; uniformity of hidden inputs by resampling one record coordinate; an accepted forgery is one of the charged events |
| `SignRho.lean`, `Rows.lean`, `RowIneq.lean`, `RowPotential.lean` | the disjoint signing lemma, per-message rows of the cache, the row potential and its charge |
| `Potentials.lean`, `StageB.lean`, `Assembly.lean`, `Main.lean` | the potentials, the two attacker stages, the bound, `forestScheme_secure` |

The architecture is described in `docs/upper-bound-proof.md`.
