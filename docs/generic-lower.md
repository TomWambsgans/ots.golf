# Generality 3/3: a lower bound for arbitrary oracle algorithms

The `generic-lower` track has a certified lower bound of 1 for every correct, available,
weakly 127-bit-secure oracle algorithm satisfying the paper's size and resource limits.
Both algorithm challenges fix signing failure at most `2^-128`.

## Paper argument

Suppose verification costs zero on every path. Each hash query costs at least one, so verification
makes no hash query, and its output is independent of the oracle table.
For a public key p and a fixed message m, call p good if some signature is accepted with probability
one. The attacker may choose such a signature by free, noncomputable deterministic computation,
which is permitted by the existing query-complexity model.

Correctness implies that every successfully returned honest signature, on every positive-probability
key-generation/signing transcript, witnesses a good public key. Thus the probability of a good public
key is at least the honest signing-success probability. With signing failure at most one half,
this probability is at least one half. This also ensures that the signature type is nonempty.

The attacker requests a signature on message 0, ignores it, and outputs its selected signature on
message 1. These are distinct 256-bit messages. For every good public key the forgery is accepted
with probability one, regardless of the oracle queries made during the intervening signing.
The attack uses no hash queries. The whole experiment costs at most 1024 + 2^20 compressions,
including key generation and the requested signature; verification costs zero by assumption.
Its success is at least 1/2, whereas 127-bit security requires success below
(1024 + 2^20) / 2^127 < 1/2. Contradiction.

The proof lemma covers every failure allowance at most 1/2. The public challenge specializes it
to `2^-128`, matching the upper track. This quantitative availability bound gives the attack
enough success probability to exceed the security threshold.

The argument uses the verifier's independence from the oracle. A verifier making one query can
depend on its answer, so a larger lower bound requires a different attack.

## Checked certificate

```lean
OptimalOTS.GenericLower.candidate :
  AlgorithmVerificationLowerBound paperParams AlgorithmScheme.paperLimits (1 / 2) 1

OptimalOTS.Challenge.GenericLower.candidate :
  AlgorithmVerificationLowerBound paperParams AlgorithmScheme.paperLimits (1 / 2 ^ 128) 1

OptimalOTS.GenericLower.paper_lowerBound_one {ε : ℝ≥0∞} (hε : ε ≤ 1 / 2) :
  AlgorithmVerificationLowerBound paperParams AlgorithmScheme.paperLimits ε 1
```

`AlgorithmVerificationLowerBound P L ε c` quantifies over every `AlgorithmScheme P`
satisfying `Admissible L ε` and `Secure`. It proves that every pathwise verification
budget is at least `c`. The attack forges on a fresh message; `AlgorithmScheme.Secure.weaklySecure`,
proved in the submission root, bridges the strong hypothesis to the weak experiment the proof
analyses.

Files:

- Protected `Algorithm.lean`: arbitrary algorithm interface and lower statement. The challenge
  fixes the paper limits and failure allowance.
- `formal/Submissions/GenericLower/WeakSecurity.lean`: the fresh-message experiment and the
  strong-to-weak bridge.
- `formal/Submissions/GenericLower/Costs.lean`: structural cost rules.
- `formal/Submissions/GenericLower/ZeroQuery.lean`: independence of zero-cost verification from the cache.
- `formal/Submissions/GenericLower/Proof.lean`: availability, public signature selection, fresh-message
  attack, experiment cost and success, and the numerical contradiction.
- `formal/Submissions/GenericLower/Solution.lean`: official export; `claim.txt` contains 1.

The in-file axiom guard for `candidate` accepts exactly `propext`, `Classical.choice` and
`Quot.sound`. The protected file contains the definitions, not the lower-bound proof; all proof
code is in the ordinary submission root.

Generic lower submission command:

```sh
python3 verifier/verify.py generic-lower --source .
```

The generic lower challenge pins the `2^-128` failure allowance. Its certificate applies the
general lemma with the exact inequality `2^-128 ≤ 1/2`.

The separate [one-query argument](research/generic-one-query.md) is research toward 2. Its
transcript lemmas await Lean proofs, and its randomized-verifier normal form is moot now that
verification is deterministic.
