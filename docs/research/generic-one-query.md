# A proposed attack on one-compression generic verification

**Status: paper argument, not a Lean certificate.** The contract now requires deterministic
verification (`AlgorithmScheme.Admissible.verifyDeterministic`), so the randomized-verifier
normal form below is moot. This note develops a route to a
generic verification lower bound of **2**, including randomized verifiers. The
normal-form and transcript lemmas below have not been formalized, so this is not
an admitted submission or a website record. The separately checked generic
lower certificate of 1 is documented in [lower-generality-3.md](../lower-generality-3.md).

The argument uses the current oracle-program interface and first-principles counting,
including randomized verification. It assumes perfect correctness, signing success at
least one half, and the paper resource limits.

## Assumptions and constants

Let `S : AlgorithmScheme paperParams` satisfy:

- `S.Correct` and `S.SigningFailureAtMost (1 / 2)`;
- key-generation cost at most `K = 1024`;
- signing cost at most `s = 2^20` on every secret key and message;
- every honest signature has an injective encoding of length at most 5376;
- verification cost at most **one** on every input and every execution path;
- the existing 127-bit `S.Secure` requirement, including honest-party costs.

There are `M = 2^256` messages. Every hash query costs at least one, so a
key-generation/signing transcript contains at most
`N = K + s < 2^22` distinct oracle inputs. A verifier query must have length at
most 512, giving a finite universe `Q` of possible verifier queries. Write

```
δ = 2^-24
τ = 2^-25
s τ = 1/16
N δ < 1/4.
```

The set `C` of message/signature pairs with signature encodings of length at
most 5376 is finite. It is nonempty by signing availability. Consequently all
maxima and selections over candidates below exist. Such searches are free in
this model: only actual calls to the shared random oracle incur cost. No
efficiency claim is made for them. In the current classical Lean interface,
pure selections may also use noncomputable functions.

## 1. The required one-query normal form

Fix a public key and a candidate `c = (m, σ)` in `C`. Average over the
verifier's free randomness. Define:

- `a_c`: probability of accepting without making a hash query;
- `u_c(q)`: probability that its sole hash query is `q`;
- `f_c(q, y)`: probability of reaching query `q` and accepting if that query is
  answered with `y`, averaging both the randomness before the query and the
  possibly answer-dependent randomness after it.

These are quantities determined by the public program and its inputs; their
definition makes no call to the actual shared oracle. They satisfy

```
0 ≤ f_c(q, y) ≤ u_c(q),       Σ_q u_c(q) ≤ 1.
```

For any fixed oracle function `O`, the actual acceptance probability is

```
A_O(c) = a_c + Σ_q f_c(q, O(q)).                         (1)
```

This is the central normal-form lemma still needed in Lean. Randomness after
the query must be included in `f`; treating a randomized verifier as a single
deterministic verification branch would not suffice.

Define an acceptance probability guaranteed for every oracle:

```
b_c = a_c + Σ_q min_y f_c(q, y)
B(pk) = max_c b_c.
```

Equation (1) gives `A_O(c) ≥ b_c` for every `O`.

## 2. Perfect correctness identifies the known queries

Consider a positive-probability honest execution up to the production of a
signature. Condition on its complete execution history, including its free
random choices, message, signature, and the oracle answers seen by key
generation and signing. Let `T` be the resulting oracle cache.

Every answer outside `T` is still independently uniform. Perfect correctness
implies that verification of this honest candidate has conditional acceptance
probability one. Since `f_c(q, y) ≤ u_c(q)`, all nonnegative rejection deficits
must vanish. In particular,

```
q ∉ T  ⇒  f_c(q, y) = u_c(q) for every y.
```

Equivalently, any verifier query the honest parties have not made must accept
every possible answer, averaged over the relevant verifier branches. There is
no assumption that the signer knows the verifier's coins.

It follows that

```
1 = b_c + Σ_(q ∈ T) [f_c(q, O(q)) - min_y f_c(q, y)]
  ≤ b_c + Σ_(q ∈ T) f_c(q, O(q)).                        (2)
```

If `B(pk) < 1/4`, then some `q ∈ T` satisfies
`f_c(q, O(q)) ≥ δ`: otherwise the right-hand side of (2) is less than
`1/4 + N δ < 1/2`.

This reasoning applies to a uniformly sampled message. The current correctness
and availability definitions quantify over deterministic public-key-dependent
message choices, which include every constant choice; averaging these finitely
many constant choices gives the same properties for an independent uniform
message.

## 3. Three concrete attackers

All three produce a message different from the one submitted to the signing
oracle. Thus the proposed argument also targets the generic weak-unforgeability
definition in `formal/Submissions/GenericLower/WeakSecurity.lean`; the upper interface requires strong
unforgeability.

### Attacker 0: guaranteed acceptance without attacker hash queries

Given `pk`, choose a candidate attaining `B(pk)`. Request a signature on any
different message, then output the chosen candidate, ignoring the answer.

Its success probability is at least `E[B(pk)]`, and its total experiment cost
is at most

```
B₀ = K + s + 1.
```

Security would therefore imply, with `e₀ = B₀ / 2^127`,

```
Pr[B(pk) ≥ 1/4] ≤ 4 E[B(pk)] < 4 e₀.                   (3)
```

Selecting the target before asking to sign a different message is essential:
the attacker does not merely output an honest signature on the signed message.

### Attacker H: query a short list of promising oracle inputs

Define

```
F(pk, q, y) = max_(c ∈ C) f_c(q, y)
p(pk, q) = Pr_uniform_y[F(pk, q, y) ≥ δ]
H(pk) = {q ∈ Q : p(pk, q) ≥ τ}.
```

Before requesting its signature, the attacker queries a fixed selection of
`min(K + 1, |H(pk)|)` distinct members of `H(pk)`. If an answer satisfies
`F ≥ δ`, it chooses a witnessing candidate, requests a signature on a
different message, and outputs that candidate. Equation (1) guarantees final
acceptance with probability at least `δ`, regardless of other oracle answers
or the behavior of the signer.

Let `Z` be the event `|H(pk)| ≥ K + 1`. Conditional on the complete keygen
history, the selected list is fixed. At least one selected query is absent
from the keygen cache. The answer to the first such query is uniform, so the
conditional chance of finding a useful answer is at least `τ`. This remains
valid even though `pk` and `H(pk)` depend on cached oracle answers: freshness
is used only after conditioning on that complete history.

If `Z` is false, the attacker queries all of `H(pk)`. Write `Y` for the event
that some member of `H(pk)` has an actual answer satisfying `F ≥ δ`. Then

```
success_H ≥ δ τ Pr[Z] + δ Pr[¬Z ∧ Y]
          ≥ δ τ Pr[Z ∪ (¬Z ∧ Y)].                       (4)
```

Its total experiment cost is at most

```
B_H = K + (K + 1) + s + 1 = 2K + s + 2.
```

With `e_H = B_H / 2^127`, security and (4) imply

```
Pr[Z ∪ (¬Z ∧ Y)] < e_H / (δ τ).                         (5)
```

### Attacker R: reuse a useful query of an honest signature

The attacker requests a signature on an independent uniform message `m`.
After receiving `some σ`, it runs the verifier once, recording its sole hash
query and answer if it makes one. This recording adds no oracle calls.

For a recorded `(q, y)`, free search finds a different message `m' ≠ m` and a
bounded signature `σ'` with `f_(m',σ')(q, y) ≥ δ`, if one exists. The attacker
outputs that candidate. If none exists, or signing returns `none`, it outputs
an arbitrary fresh-message candidate; such fallback behavior contributes
nothing to the claimed success bound.

For any `(pk, q, y)`, define

```
Messages(pk, q, y) = {m : ∃ bounded σ, f_(m,σ)(q, y) ≥ δ}.
```

Let `G` be the event that an honest signature `c = (m, σ)` is returned and
some keygen query `q` satisfies both

```
f_c(q, O(q)) ≥ δ,       |Messages(pk, q, O(q))| ≥ 2.
```

Fix any oracle and honest history in `G`, and select a witnessing `q`.
The replayed verifier reaches it with probability
`u_c(q) ≥ f_c(q, O(q)) ≥ δ`. Once that happens, a candidate for another
message exists and has final acceptance probability at least `δ` by (1).
The fresh verification coins are independent of the replay coins. Hence

```
success_R ≥ δ² Pr[G].                                   (6)
```

The total experiment cost is at most

```
B_R = K + s + 1 + 1 = K + s + 2.
```

Writing `e_R = B_R / 2^127`, security gives

```
Pr[G] < e_R / δ².                                       (7)
```

## 4. Account for every successful honest signature

Run honest key generation and signing on an independent uniform message.
Signing succeeds with probability at least one half. By perfect correctness,
apart from a null event, every produced signature satisfies (2).

Remove histories with `B(pk) ≥ 1/4`, and histories in
`Z ∪ (¬Z ∧ Y)`. On every remaining successful history, equation (2) supplies
a useful query `q ∈ T` with `f_c(q, O(q)) ≥ δ`, hence `F(pk, q, O(q)) ≥ δ`.
Such a query is outside `H(pk)`, since no member of `H(pk)` has a useful
actual answer on these histories.

There are three possibilities:

1. **The query was fresh during signing.** At each first query to a new input
   outside `H(pk)`, the conditional chance of `F ≥ δ` is less than `τ`.
   There are at most `s` signing queries, so a union bound gives at most
   `s τ = 1/16`. The adaptive query choice and the secret key do not change
   this bound: condition on the entire history before the fresh answer.
2. **It was a keygen query and its useful-message set has size one.**
   Conditional on keygen, these singleton message sets are already fixed.
   Their union contains at most `K` messages. An independent uniform requested
   message hits them with probability at most `K/M = 2^-246`.
3. **It was a keygen query and its useful-message set has size at least two.**
   This is event `G`, covered by attacker R.

Therefore the three security inequalities would force

```
1/2 ≤ signing success
    ≤ 4e₀ + e_H/(δτ) + sτ + K/M + e_R/δ².              (8)
```

Every attack budget above is less than `2^22`, so `e₀, e_H, e_R < 2^-105`.
The right side of (8) is strictly less than

```
2^-103 + 2^-56 + 1/16 + 2^-246 + 2^-57 < 1/8,
```

a contradiction. These constants have substantial slack; there is no numerical
optimization at issue.

## Audit and formalization boundary

No fatal gap was identified in this paper argument, but the following are
actual proof obligations, not established Lean facts:

- A one-compression oracle program has the weighted normal form (1), including
  arbitrary free sampling before and after its query and zero-query branches.
- Static random-function semantics agree with the existing lazy-cache
  semantics. In particular, making additional observations does not change
  the underlying oracle, and fresh answers remain uniform after conditioning
  on a complete adaptive transcript.
- Perfect correctness implies the outside-cache equality used in (2), after
  conditioning on each possible honest history. Conditioning on the public
  key alone is insufficient for this step.
- The bounded candidate set is finite, the extrema are attained, and the
  three classical selections define admissible oracle programs with the
  stated all-path cost bounds.
- Query tracking for attacker R preserves the verifier's query distribution
  and cost, and all attacks satisfy the fresh-message condition.
- The finite-message averaging, adaptive fresh-query union bound, and event
  partition leading to (8) hold in the library's probability representation.

The smallest useful next formal component is the **one-query weighted
normal-form lemma**. The zero-cost oracle-independence lemma needed for the
bound of 1 should handle the continuation after the unique hash query. A
normal-form proof should expose the nonnegative coefficients `a`, `u`, and
`f`, their mass bounds, and the acceptance identity for every deterministic
oracle table. It is reusable independently of the signature argument.

After that, the most valuable separate component is a transcript lemma:
perfect acceptance under uniformly fresh answers forces acceptance under
every possible fresh answer. Neither component requires touching the existing
DAG or upper-reference submissions.

This argument does **not** establish a bound of 3. With two verifier queries,
the second query can depend on the first answer, and acceptance is no longer
the additive single-query expression (1). Extending this method would require
a new analysis of those dependencies.

## Statement audit for higher generic lower claims (2026-09-18)

The exported statement is `AlgorithmVerificationLowerBound paperParams paperLimits (1 / 2 ^ 128) c`:
for every `AlgorithmScheme paperParams` that is `Admissible paperLimits (1 / 2 ^ 128)` and
`WeaklySecure`, every pathwise verification budget `v` satisfies `c ≤ v`. The following facts
were checked against the protected definitions and the library semantics, so that a proof of
`2` (or more) targets a meaningful statement rather than a modeling artifact.

- **Not vacuous.** `Admissible paperLimits (1 / 2 ^ 128)` and `WeaklySecure` are jointly
  satisfiable: the kernel-checked forest (`GenericUpperForest.admissible`, `GenericUpperForest.secure`
  with `Secure.weaklySecure`) meets both with `VerifyCostAtMost 106`. Hence every claim `c ≤ 106`
  says something about real schemes, and `c ≥ 107` is false. A proof of `2` cannot come from
  unsatisfiable hypotheses.
- **Cost one means one short query.** `blockCost P k = max 1 ⌈k / 512⌉ ≥ 1`, so `CostAtMost 1`
  allows at most one hash query per path, of at most 512 input bits; uniform sampling costs zero
  and is never cached. The finite query universe `Q` in Section 1 is therefore exact.
- **One shared lazy table.** `oracleImpl` answers every hash query through `randomOracle`: a cached
  answer if the input was queried before by any party, otherwise a fresh uniform 256-bit answer
  that is then cached. The "fresh answers remain uniform after conditioning on a complete
  transcript" step is a property of this implementation, not an extra assumption.
- **Perfect correctness.** `Correct` requires rejection probability exactly zero for every
  deterministic public-key-dependent message choice; constant choices give uniform messages by
  averaging. `SigningFailureAtMost (1 / 2 ^ 128)` gives honest signing success at least one half,
  as used by the existing certificate of 1 through `paper_lowerBound_one`.
- **Attack budgets include honest parties.** `WeaklySecure` bounds success by `B / 2 ^ 127` for
  every pathwise budget `B` of the whole experiment. The three attacks of Section 3 cost at most
  `2K + s + 2 < 2 ^ 22`, so each security inequality contributes less than `2 ^ -105`.
- **Weak security is the right target.** Every attack forges on a message other than the signed
  one, as `weakExperiment` requires; strong security implies weak security, so a proved bound also
  covers strongly secure schemes.
- **Finite candidate sets.** `encodeSignature` is injective and `RejectsOversized 5376` rejects
  longer encodings on every path, so the candidate set `C` of Section 1 is finite and all maxima
  exist. Selections may be classical: only hash queries are charged.
- **One harmless quirk.** A scheme admitting an adversary whose whole experiment is query-free
  would need success below `0 / 2 ^ 127`, which is impossible, so such a scheme is insecure by
  definition. Any scheme whose key generation hashes on every path is unaffected.

No definition change is needed. The remaining work is proof engineering: the one-query
normal-form lemma and the transcript lemma listed above, then the accounting of Section 4.
