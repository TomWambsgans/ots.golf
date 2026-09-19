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


## Option 2: the disjoint-event signing lemma (2026-09-19, follow-up)

Notation at signing time for the signed message `m1`: `I = 2^128` index values, `M = numValid`
accepted indices, `q = M / I`; `V` the set of distinct accepted indices held by cached encoding
entries, `r = |V| / M`; for message `m`: `a_m` cached accepted `m`-entries, `b_m` of them sharing
their index with another cached entry (the set `W`), `N_m` uncached `m`-nonces. `L = 2^20`.

### 1. The signing lemma (paper proof, complete)

At a trial with `U` untried nonces of which `NF` are uncached, the signer stops on a cached
accepted nonce with probability `a / U` (bad for `b` of them) and on a fresh accepted answer with
probability `q NF / U` (bad with probability `r`, the index being uniform over the accepted set).
So bad mass `≤ ρ ·` stop mass at every trial, with

    ρ = max_{c ∈ [N − L, N]} f(c),   f(c) = (r q c + b) / (a + q c) = r + (b − r a) / (a + q c),

and by induction over the trials, `E[1_bad] ≤ ρ · P(stop) ≤ ρ`. This replaces the union
`r + L · pairs / (2^n − L)` by one disjoint case split, and `ρ ≤ r + (b − r a)^+ / (a + q (N − L))`.
The induction step is exactly the one of `signIdxLoop_bound`, with the continuation value
`F + λ ρ · [no signature]` in place of `F`. This part is ready to formalize.

### 2. The stage-A potential (the open part)

The attacker chooses `m1` after stage A, so the potential must dominate `max_m G_m` with
`G_m = r + (b_m − r a_m)^+ / (a_m + q (N_m − L))`, and grow by at most `κ = 2^-127` per encoding
query (encoding queries charge nothing else; `384 ∉ {144, 400, 912}`).

* **One message (proved on paper, checked numerically).** With `D = a + qN`, one fresh encoding
  query at `m` changes `G_m` by at most `ε (a + q(N−1) − (N−1)|V|/I) / D ≤ ε`, `ε = 2^-128`:
  invalid answers move `G` by `q (G − r) / (D − q)`, fresh accepted indices raise `r`, hits on `V`
  raise `b`. `tools/nonce128_own_charge.py` evaluates the exact expectation on 40,000 random states
  in the regime `N ≥ I/2` (guaranteed by `encCount ≤ 2^127`): worst charge `0.987 ε`. So an attacker
  who concentrates on one message is charged half of `κ`, and the target holds with room to spare.
* **Several messages (numerically, no proof yet).** A query at `m0` can also raise `G_h` for the
  message `h` whose entry it collides with, by `1/D_h`. Summing these jumps over messages
  (a `Σ_m` potential) charges up to `ε(1 + 2r)` and fails above `B ≈ 2^128/3`; the maximum only pays
  a jump when `G_h + 1/D_h` exceeds the current maximum. `tools/nonce128_max_charge.py` computes
  the exact expected increase of `max_m G_m` on 3,000 adversarial states (many single-entry
  messages, colliding pairs, mixed, large messages; every choice of queried message): worst
  `0.999 ε`, below `κ = 2 ε` with a factor-2 margin.
* **What a proof needs.** Bound `E[max_m G'_m] − max_m G_m ≤ 2 ε` by the three outcome classes
  (invalid answer: only `G_{m0}` moves, by `q (G_{m0} − r)^+ / (D_0 − q)`; fresh accepted index:
  every `G_m` moves by at most `1/M`, total `ε (1 − r)`; hit on `V`: `G_{m0}` moves by at most
  `(δ − G_{m0}) / D_0`, `δ ∈ {1, 2}`, and the holder's `G_h` by `1/D_h`, which raises the maximum
  only by `(G_h + 1/D_h − Φ)^+ ≤ min(1, (b_h − r a_h + 1)^+) / D_h`) and the constraints `D_m ≥ M/2`,
  `Σ_m (a_m − b_m) ≤ |V|`. The per-class bounds above sum to about `(1 − r) + 2(G_{m0} − r)^+ +
  (|V|(1 − G_{m0}) + a_0 − b_0)/D_0 + Σ_m (a_m − b_m) min(1, (b_m − r a_m + 1)^+)/D_m` (in units of
  `ε`), which is `≤ 2` on every state tried, but a clean inequality over all states is not proved.

### 3. Status and cost of finishing

Nothing in the contract or the roots changed: `paperParams.nonceBits` is still 256. Finishing
option 2 needs (1) a rigorous proof of the multi-message bound in section 2, (2) a new signing
lemma in the Lean roots (section 1), (3) replacing the global `encTerm` (`cntV / numSets + L ·
pairs / (2^n − L)`) in `Potentials.ΦA` by `max_m G_m`, a maximum over all `2^256` messages of
ratios, with the charge lemma of (1), and (4) doing this in the four upper roots (`GenericUpper`,
`RiscvUpper`, and the historical `Upper`, `DisclosureUpper`), fixing the 512-bit index-query length
in `Values.lean`, and then the parameter switch itself (lower roots already build at 128 bits).
Step (1) is new mathematics; steps (2)–(4) are a multi-week Lean effort.
