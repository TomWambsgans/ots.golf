# A 128-bit nonce: what breaks and why (2026-09-19)

Question: can the competition move from `paperParams.nonceBits = 256` to 128 bits (the SPHINCS+
convention at 128-bit security) while keeping the signature budget, the strong-unforgeability
target `probTrue < B / 2^127` for every budget `B`, and all current claims?

**Status (2026-09-19): done.** The contract now has `nonceBits := 128`, and every root is
kernel-checked at its claim (section 4). The sections below record the obstacle and its proof.

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

### 2. The stage-A potential: a complete proof

**Notation.** `I = 2^128` (indices, and nonces per message), `M = numValid`, `q = M/I`, `ε = 1/I`,
`κ = 2ε`, `L = 2^20`. For a cache `c`: `V` the distinct accepted indices of cached encoding
entries, `v = |V|`, `r = v/M`. An accepted entry is in `W` when another cached entry has the same
index. For a message `m`: `u_m` cached entries of row `m`, `a_m` accepted ones, `b_m` of those in
`W`, `d_m = a_m − b_m`, `N_m = I − u_m`, `D_m = a_m + q N_m`, `x_m = b_m − r a_m`,
`P_m = x_m^+ / D_m`. The invariant `encCount + budget ≤ 2^127` gives `Σ_m u_m ≤ I/2`, hence
`N_m ≥ I/2` and `D_m ≥ M/2`.

**Potential.** `Ψ(c) = r + Σ_m P_m`, and the encoding term of `ΦA` is `θ Ψ` with
`θ = I/(I − 2L)`. `Ψ(∅) = 0`, non-encoding queries do not change `Ψ`.

**It dominates the signing loss.** For the signed message (drop the index `m1`), and every
`c ∈ [N − L, N]`: `b + c·v/I = r (a + q c) + x ≤ r (a + q c) + x^+`, and
`a + q c ≥ (c/N) D ≥ ((N − L)/N) D ≥ D/θ` (as `N ≥ I/2`), so
`b + c·v/I ≤ (a + q c) (r + θ x^+/D) ≤ (a + q c) · θΨ`. This is the hypothesis `ρ = θΨ` of the
signing lemma of section 1.

**Charge of one encoding query.** Query the fresh point `(m0, η0)`; its answer's index is uniform.
Write `D0, x0, …` for the row `m0`.

1. Rejected index (`I − M` indices): only `N0` drops by one, so `Ψ` grows by
   `x0^+ q / (D0 (D0 − q))`.
2. Accepted index outside `V` (`M − v` indices): `r` grows by `1/M`; every `x_m` decreases
   (`x0' = b0 − (r + 1/M)(a0 + 1)`) and `D0' = D0 + 1 − q ≥ D0`, so every `P_m` decreases. `Ψ`
   grows by at most `1/M`.
3. Index in `V` (`v` indices): `r` is unchanged. The new entry joins `W`, and so does the holder
   when it held the index alone and was not in `W`: `x0' = x0 + δ − r` with `δ = 2` when that
   holder is in row `m0`, else `δ = 1`, and `D0' ≥ D0`, so `P0` grows by at most `(δ − r)/D0`; a
   holder in another row `h` raises `P_h` by at most `1/D_h`. Every non-`W` accepted entry holds
   its own index, so over the `v` indices these add up to
   `(v(1 − r) + d0)/D0 + Σ_{h ≠ m0} d_h / D_h`.

Averaging, `I (E[Ψ'] − Ψ) ≤ T` with
`T = (1 − q) M x0^+ / (D0 (D0 − q)) + (1 − r) + (v(1 − r) + d0)/D0 + Σ_{h ≠ m0} d_h/D_h`.

*Other rows.* `D_h = a_h + M − q u_h ≥ d_h + M − t_h` with `t_h = q u_h ≤ M`, and
`d/(d + M − t) ≤ (d + t)/M` (equivalent to `0 ≤ d² + t(M − t)`). Non-`W` entries have distinct
indices, so `Σ_{h≠m0} d_h ≤ v − d0`, and `Σ_{h≠m0} t_h ≤ M/2 − s0` with `s0 = q u0`. Hence
`Σ_{h≠m0} d_h/D_h ≤ r − d0/M + 1/2 − s0/M` and

    T ≤ 3/2 + R,   R = r(1 − r) M / D0 + (1 − q) M x0^+/(D0(D0 − q)) − s0/M − d0/M + d0/D0.

*The row `m0`.* Let `w = M − s0 ∈ [M/2, M]`, so `D0 = a0 + w`. Since `d0 ≤ a0`,
`d0/D0 − d0/M − s0/M ≤ −(s0/M)(1 − d0/D0) ≤ −(s0/M)(w/D0) = −(M − w) w/(M D0)`. Since `D0 ≥ 1`,
`(1 − q)/(D0 − q) ≤ 1/D0`, and `x0^+ ≤ (1 − r) a0`. So
`R ≤ (1 − r) M (r D0 + a0)/D0² − (M − w) w/(M D0)`, and by `4XY ≤ (X + Y)²` with
`X = (1 − r) D0`, `Y = r D0 + a0`, `(1 − r)(r D0 + a0) ≤ (2 D0 − w)²/(4 D0)`. With
`y = w/D0 ∈ (0, 1]` and `ω = w/M ∈ [1/2, 1]`:

    R ≤ y ((1 − y/2)²/ω − (1 − ω)) ≤ y · max((1 − y/2)², 2(1 − y/2)² − 1/2) ≤ 1/3,

the middle step because the bracket is convex in `ω` (so maximal at `ω ∈ {1/2, 1}`), the last by
calculus (`y(1 − y/2)² ≤ 8/27` and `y(3/2 − 2y + y²/2) ≤ 0.316`).

So `T ≤ 11/6`, and one encoding query raises `θΨ` by at most `θ · (11/6) · ε ≤ 2ε = κ`, since
`θ ≤ 12/11`. Together with section 1 this proves the signing part of the security bound for a
128-bit nonce and every budget up to `2^127`: the potential argument is otherwise unchanged
(non-encoding queries still pay `κ` for hidden keygen points and second preimages, and the
post-signing index event `IdxPost` still costs `ε` per query).

Numerical checks ([`nonce128_own_charge.py`](archive/nonce128_own_charge.py), [`nonce128_max_charge.py`](archive/nonce128_max_charge.py), and the exact
expected increase of `Ψ` on random multi-row states) all stay near `ε`, well below `11/6 ε`.

### 3. Plan of the formalization

1. `SignIdx`: a signing lemma taking any `ρ` with `b + c·v/I ≤ ρ (a + q c)` for
   `c ∈ [N − L, N]`, proved by the induction of `signIdxLoop_bound` on
   `F + λ ρ · [no signature]`.
2. `EncCharges`/`Potentials`: row counts, `Ψ`, its transitions under one encoding answer, the
   three class bounds, the row-budget sum, the inequality `T ≤ 11/6`, and `encTerm = θ Ψ` with its
   charge lemma replacing `cntV`/`pairs`.
3. `Assembly`: apply the new signing lemma with `ρ = encTerm d`.
4. Port to `RiscvUpper` (accepted set `validSet`), `Upper`, `DisclosureUpper`; fix the 512-bit
   index-query length in `Values.lean`; set `nonceBits := 128`.

## 4. Result: the contract at 128 bits (2026-09-19)

The plan of section 3 is carried out in all four upper roots. The contract changes are
`paperParams.nonceBits := 128` (`Statement.lean`), `paperLimits.signatureBits := 5376`
(`Algorithm.lean`), and the machine loading at most 5376 signature bits with the length capped at
5377 (`RiscvMachine.lean`). `maxRevealBits` stays 5248: the payload budget, the cuts and every
cost are unchanged, and the signature shrinks by the 128 nonce bits that are no longer sent.

New modules, identical in `GenericUpper`, `Upper` and `DisclosureUpper` and ported to the
accepted set `validSet` in `RiscvUpper`:

| Module | Content |
|---|---|
| `SignRho` | `signRho_bound`: the disjoint signing lemma of section 1 for any `ρ` |
| `RowIneq` | `charge_le`: the real inequality `T ≤ 11/6` for the queried row |
| `Rows` | per-message rows of the cache and their change under one fresh answer |
| `RowPotential` | `psi`, `psi_step`, `sum_gCls_le`, `psi_charge` and `psi_dom` |

`Potentials.encTerm` is now `θ · psi`, `encTerm_avg_le` follows from `psi_charge`, and
`Assembly.stageA_cont` applies `signRho_bound` with `ρ = encTerm d`, whose hypothesis is
`psi_dom`. The index query has 384 bits (`Values.len_hashParent_ne_enc`). The earlier
`cntV`/`pairs` lemmas remain in `SignIdx` and `EncCharges` but are no longer used by the proof.

| Root | Claim before | Claim after |
|---|---:|---:|
| `GenericUpper` | 106 | 106 |
| `RiscvUpper` | 1632 cycles | **1628 cycles** |
| `Upper` (historical) | 106 | 106 |
| `DisclosureUpper` (historical) | 106 | 106 |
| `Lower` | 18 | 18 |
| `DisclosureLower` | 93 | 93 |
| `GenericLower` | 1 | 1 |

The RISC-V index prefix now copies one 16-byte nonce block instead of two and hashes 384 bits,
four instructions fewer: the image has 2647 instructions, the index phase costs 267 cycles, and the
payload starts at `signatureBase + 16`. The security bound is unchanged: `(B − 912)/2^127` for
every budget `B ≤ 2^127`.

