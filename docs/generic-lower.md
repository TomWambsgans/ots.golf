# Generality 3/3: a lower bound for arbitrary oracle algorithms

The `generic-lower` track has a certified lower bound of 1 for every correct, available,
weakly 127-bit-secure oracle algorithm satisfying the paper's size and resource limits.
Both algorithm challenges fix signing failure at most `2^-128`.

## Paper argument

Suppose verification costs zero on every path. Each hash query costs at least one, so verification
uses only its private randomness. Its output distribution is independent of the oracle table.
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
The attack uses no hash queries. The whole experiment costs at most 1024 + 2^21 compressions,
including key generation and the requested signature; verification costs zero by assumption.
Its success is at least 1/2, whereas 127-bit security requires success below
(1024 + 2^21) / 2^127 < 1/2. Contradiction.

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
satisfying `Admissible L ε` and `WeaklySecure`. It proves that every pathwise verification
budget is at least `c`. `AlgorithmScheme.Secure.weaklySecure` also checks in Lean, so the
result covers all strongly secure schemes meeting those admissibility requirements.

Files:

- Protected `Algorithm.lean` and `AlgorithmWeak.lean`: arbitrary algorithm interface, weak experiment,
  strong-to-weak bridge and lower statement. The challenge fixes the paper limits and failure allowance.
- `formal/Submissions/GenericLower/Costs.lean`: structural cost rules.
- `formal/Submissions/GenericLower/ZeroQuery.lean`: independence of zero-cost verification from the cache.
- `formal/Submissions/GenericLower/Proof.lean`: availability, public signature selection, fresh-message
  attack, experiment cost and success, and the numerical contradiction.
- `formal/Submissions/GenericLower/Solution.lean`: official export; `claim.txt` contains 1.
- `OptimalOTS/AlgorithmLower.lean` and `AlgorithmZeroQuery.lean`: compatibility imports only.

`lake build Submissions.GenericLower.Solution OptimalOTS.AlgorithmLower` and the complete
`lake build OptimalOTS Submissions` (8897 jobs) pass. The in-file axiom guard for `candidate` accepts
exactly `propext`, `Classical.choice` and `Quot.sound`. There are no admitted proofs or
`native_decide` calls. The official comparator accepts claim 1. The protected files contain the
definitions, not the lower-bound proof; all proof code is in the ordinary submission root.

Generic lower submission command:

```sh
python3 verifier/verify.py generic-lower --source .
```

The generic lower challenge pins the `2^-128` failure allowance. Its certificate applies the
general lemma with the exact inequality `2^-128 ≤ 1/2`.

The separate [one-query argument](generic-one-query.md) is research toward 2. Its normal-form and
transcript lemmas await Lean proofs; the certified claim remains 1.

## Local website

The card, chart, leaderboard and solver profile link to the same persistent Vitalik demo at claim 1.
All four public tracks are open. Rules state the shared `2^-128` algorithm availability threshold,
admissibility, encoding, DAG and submission requirements in expandable sections.

All 15 service tests pass, covering the generic lower queue and pull-request root mapping,
score-independent rules, framework isolation, Vitalik's linked generic submission and preservation of demo rows. A proof or admission
change must now update the website, metadata, rules and documentation in the same change.
Headless Firefox checks pass for the three lower lines and tables, generic lower's open status,
the simplified top navigation, direction switches, sorting, keyboard chart tooltips, filtered
deep links, rules expansion, and a narrow layout without page overflow.

## Verification

The public challenge now fixes `2^-128`, shared with the upper track. The updated certificate
applies `paper_lowerBound_one` and proves `2^-128 ≤ 1/2` with exact arithmetic. The official
verifier accepted claim 1 in 53.0 seconds under pin
`fd04517f1f73521d46ca98afb9c7e43d34df60f7d9fded3a1fdcb9817c3023fb`.
A temporary submission using the stricter `2^-256` allowance compiled successfully and was
rejected for a statement mismatch in 58.8 seconds. Full validation is recorded in
[the production review](production-readiness.md).

### Original one-half challenge

The contract pin is `6c2eb7a11e4b3cc1` (19 protected files). Existing DAG and partial-disclosure
definitions and all four original submission roots are unchanged. The additions pin the generic
definitions, challenge and comparator configuration.

`generic-lower`, claim 1: **verified**, 55.0 seconds. Log:
`/private/var/folders/7g/qxrr2pgj40s3ykbngr10jkkr0000gn/T/ots-verify-4cy8xbv6/verify.log`.

A separate temporary copy with `claim.txt` changed to 2 and its proof left at 1 was **rejected**
by comparator in 54.3 seconds. Log:
`/private/var/folders/7g/qxrr2pgj40s3ykbngr10jkkr0000gn/T/ots-verify-x77myj5i/verify.log`.

DAG lower regression, claim 18: **verified**, 126.7 seconds. Log:
`/private/var/folders/7g/qxrr2pgj40s3ykbngr10jkkr0000gn/T/ots-verify-78l9no3y/verify.log`.

Legacy DAG upper regression, claim 106: **verified**, 171.7 seconds. Log:
`/private/var/folders/7g/qxrr2pgj40s3ykbngr10jkkr0000gn/T/ots-verify-ffx7_3q5/verify.log`.
