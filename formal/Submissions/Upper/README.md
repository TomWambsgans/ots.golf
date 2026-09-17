# Upper track baseline: the flat scheme, 109 units

41 hash chains of length 20 whose ends are hashed together into the root. With the contract's cost
model (one unit per started 512-bit block of the input plus 192 overhead bits) a chain hash costs
one unit, the root (5248 bits) eleven and the message index two. A signature reveals one 128-bit
value on every chain, at positions chosen so that the verifier recomputes exactly 96 chain hashes:
every signature verifies in `2 + 11 + 96 = 109` units, the `comp 41 96 ≥ 2 ^ 115` such position
vectors give the disclosure sets, and the scheme meets the 127-bit strong-unforgeability
requirement of `OptimalOTS/Statement.lean`. The proof gives `Pr[forge] ≤ (B - 831) / 2 ^ 127` for
every budget `B ≤ 2 ^ 127`.

Exports (`Solution.lean`): `OptimalOTS.Challenge.Upper.scheme`, `secure`, `cost`.

## Files

| File | Content |
|---|---|
| `Semantics.lean` | records, deterministic evaluation, reconstruction with oracle tables (shared with the lower track; copied, since submissions cannot import each other) |
| `Cache.lean`, `IUB.lean`, `Master.lean` | the lazy random oracle's cache; the identical-until-bad coupling; the supermartingale master lemma (a potential growing by at most `κ` per unit of query cost bounds a bad event by `κ · budget`) |
| `Keygen.lean`, `Reconstruct.lean`, `SignIdx.lean`, `EncCharges.lean` | key generation as a uniform record; the verifier's run; the signing loop; charges of encoding queries |
| `Names.lean`, `Tree.lean` | the 1683-node computation graph; the tree structure, visited sets, costs, cuts |
| `Count.lean`, `Cuts.lean`, `Scheme.lean` | the disclosure family (`comp 41 96` position vectors, counted by kernel computation) and `forestScheme` |
| `Values.lean`, `Resample.lean`, `Events.lean` | node values; hidden and exposed keygen points; uniformity of hidden inputs by resampling one record coordinate; an accepted forgery is one of the charged events |
| `Potentials.lean`, `StageB.lean`, `Assembly.lean`, `Main.lean` | the potentials, the two attacker stages, the bound, `forestScheme_secure` |

The architecture is described in `docs/upper-bound-proof.md`.
