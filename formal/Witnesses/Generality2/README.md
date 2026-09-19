# Generality 2/3 witness: the 106-compression forest

An internal maintainer check, not a track and not a submission. The Generality 2/3 lower bound
quantifies over secure DAG schemes; this proof shows that class is non-empty.
[`../Generality2.lean`](../Generality2.lean) states

```lean
theorem OptimalOTS.Witnesses.generality2 :
    ∃ S : Scheme, S.Secure ∧ ∀ i, S.verifyCost i ≤ 106
```

Check it from `formal/` with `lake build Witnesses` (also run by `tools/check_repo.py --formal`).

## Construction

The forest of Section 7 of the paper: 63 hash chains of length 14 whose ends are grouped three by
three into 21 group digests, grouped three by three into 7 subtree digests, hashed together into
the root. With a single oracle and no domain separation, the scheme separates its hash nodes
itself: every hash input starts with a 16-bit tweak naming its node (`tw`, in `Names.lean`).

- A chain step hashes 144 bits, a grouping hash 400 and the root 912; none has the 384 bits of an
  index query. Chain and grouping hashes cost one compression, the root two.
- A signature reveals one 128-bit value on every source-to-root path. The `2 ^ 115` disclosure sets
  are cuts of reconstruction cost 105 with at most 41 revealed values, so every signature verifies
  in `1 + 105 = 106` compressions.
- Security: `Pr[forge] ≤ (B - 912) / 2 ^ 127` for every budget `B ≤ 2 ^ 127`.

## Files

| File | Content |
|---|---|
| `Semantics.lean` | records and deterministic evaluation |
| `Cache.lean`, `IUB.lean`, `Master.lean` | the lazy random oracle's cache; the identical-until-bad coupling; the supermartingale master lemma (a potential growing by at most `κ` per compression bounds a bad event by `κ · budget`) |
| `Keygen.lean`, `Reconstruct.lean`, `SignIdx.lean`, `EncCharges.lean` | key generation as a uniform record; the verifier's run; the signing loop and the vocabulary of its bound; the encoding-entry count and the `IdxPost` charge |
| `Names.lean`, `Tree.lean` | the 2795-node computation graph; the tree structure, visited sets, costs, cuts |
| `Count.lean`, `Cuts.lean`, `Scheme.lean` | the disclosure family (more than `2 ^ 115` sets, certified by kernel computation) and `forestScheme` |
| `Values.lean`, `Resample.lean`, `Events.lean` | node values; hidden and exposed keygen points; uniformity of hidden inputs by resampling one record coordinate; an accepted forgery is one of the charged events |
| `SignRho.lean`, `Rows.lean`, `RowIneq.lean`, `RowPotential.lean` | the disjoint signing lemma, per-message rows of the cache, the row potential and its charge |
| `Potentials.lean`, `StageB.lean`, `Assembly.lean`, `Main.lean` | the potentials, the two attacker stages, the bound, `forestScheme_secure` |

The proof architecture is described in [upper-bound-proof.md](../../../docs/upper-bound-proof.md).
