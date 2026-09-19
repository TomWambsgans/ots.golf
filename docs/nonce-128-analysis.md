# A 128-bit nonce: what breaks and why (2026-09-19)

Question: can the competition move from `paperParams.nonceBits = 256` to 128 bits (the SPHINCS+
convention at 128-bit security) while keeping the signature budget, the strong-unforgeability
target `probTrue < B / 2^127` for every budget `B`, and all current claims?

## Experiment

With only `nonceBits := 128` changed in `OptimalOTS/Statement.lean`:

| Root | Result |
|---|---|
| `Lower` (Generality 2/3, claim 18) | builds unchanged |
| `DisclosureLower` (Generality 1/3, claim 93) | builds unchanged |
| `GenericLower` (Generality 3/3, claim 1) | builds unchanged |
| `GenericUpper` (106), `RiscvUpper` (1632), historical `Upper`, `DisclosureUpper` | fail |

The lower bounds are attacks, and their counting never needs a long nonce. The upper roots first
fail on a hard-coded 512-bit index-query length (`Values.lean`, easy to fix). The real obstacle
is the signing-loop charge in the security proof.

## The obstacle

The security proof bounds the attacker by a potential that must grow, on average, by at most
`κ = 2ε = 2^-127` per compression. A non-encoding query spends its whole `κ` on the hidden-keygen
and second-preimage events. An encoding query (`H(m ‖ η)`) spends `ε` on the "index guess" event
(the signer's fresh index lands on an index the attacker already holds: `|V| / numSets`, which grows
by exactly `q / numSets = 2^-128` per query, `q = numSets / 2^128`), and the remaining `ε` must pay
for the "pairs" event: the signer's nonce is one the attacker queried in advance, and that entry's
index is shared with another entry, giving a strong forgery (same cut, other nonce or message).

Today that event is bounded by a union over the `2^20` trials,
`trialLimit · pairs / (2^nonceBits − trialLimit)`, with per-query charge
`2^20 · 2 · encCount / (2^128 (2^nonceBits − 2^20))`. It fits in `ε` iff `2^148 ≲ 2^nonceBits`.

Sharper, and correct at any nonce length: the signer stops at the first valid index, so it ends at
a given pre-queried valid nonce with probability at most `1 / (q N)`, where `N ≥ 2^128 − e − L` is the
number of untried, unqueried nonces (`e` encoding entries so far). The pairs event is then at most
`c · pairs` with `c = 1 / (q N)`. The trouble is how `pairs` grows: a fresh encoding answer adds
`2 · cntV / 2^128` pairs in expectation, where `cntV` is the number of valid entries already cached,
a random quantity chosen adaptively by the attacker. A cache-only potential with a constant charge
must reserve for future pairs:

    Ψ = c · (pairs + 2 · cntV · b / 2^128),   b = remaining budget,

whose expected growth on an encoding query is exactly `2 c q (b − 1) / 2^128 = 2(b − 1) / (2^128 N)`
and which never grows on other queries. With `c` fixed from the total budget (`N ≥ 2^128 − B`), this
is at most `ε` iff `2B ≤ 2^128 − B`, that is **`B ≤ 2^128 / 3`**. So the proof extends to 128-bit
nonces for every budget up to about `2^126.4`.

For `B` between `2^128/3` and `2^127` the reserve over-charges: it pays up front for pairs with
every future query, and when the attacker later spends its budget on non-encoding queries the refund
is proportional to the random `cntV`, which a deterministic budget account cannot use. Worst case
(encoding queries first, the rest spent elsewhere) the bound exceeds `B / 2^127` by up to `1/8` at
`B = 2^127`. Charging pairs when they form instead (no reserve) has the right total,
`E² / (2^128 (2^128 − B))` for `E` encoding queries, which fits exactly because `E ≤ 2^127`; but its
per-query charge depends on the random `cntV`, and an adaptive attacker can bias it. The leftover
slack at `B ≈ 2^127` is only the keygen margin, about `2^-116`, far below what any concentration
argument gives.

The underlying reason: with a 128-bit nonce, `2^127` queries cover half of the signer's nonce
space. The true attack success stays below the bound (the index-guess and pairs events are
disjoint: the signer ends either on a fresh nonce or on a cached one), but a proof that keeps them
as separate union terms is exact to within `2^-116` at the top of the range, and ours is not.

## Options

1. **Keep 256 bits** (current contract). Nothing changes.
2. **Prove the disjoint-event version.** Bound the bad event by
   `(|W_m1| + μ · |V| / numSets) / (cntV_m1 + μ)` with `μ = q N` (the signer ends either on one of the
   `cntV_m1` cached valid nonces or on a fresh one), and build a potential for this ratio. This is a
   new signing lemma and new potentials in both upper roots: research-level work, not a refactor.
3. **Split the parameter.** Set `nonceBits := 128` for the DAG model only (the three lower roots
   already build), and let the upper algorithm schemes keep a 256-bit nonce inside their own signature
   encoding. The algorithm interface prescribes no nonce format, and 256 + 5248 still fits the 5504-bit
   budget. This needs the upper roots to be built over a parameter record with `nonceBits = 256`,
   whose `AlgorithmScheme` coincides with the one over `paperParams` (only hash, key and message widths
   matter there). The practical constructions would then still use 256-bit nonces.
4. **Lower the target** to about `B / 2^126.4` for 128-bit nonces. This weakens the security
   statement and needs a decision by the organisers.
