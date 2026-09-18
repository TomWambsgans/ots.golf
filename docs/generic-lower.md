# A first lower bound for arbitrary oracle algorithms

The open `generic-lower` track has certified baseline 1: a correct, available, weakly
127-bit-secure generic scheme cannot verify every input with zero compressions. It makes no
DAG, cut, nonce, domain-separation or signature-format assumption.

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

The lower challenge pins a deliberately weak 1/2 failure allowance. The theorem covers every
stricter allowance without selecting the final generic upper admission threshold. The interface's
general condition that failure is merely less than one is insufficient: successful signing could
otherwise be far rarer than the security threshold.

This argument proves only one compression. A one-query verifier still depends on the secret oracle
table, so its accepting signatures cannot simply be selected by free public computation. A bound of
two or three requires another argument; it does not follow by repeating this proof.

## Checked certificate

```lean
OptimalOTS.GenericLower.candidate :
  AlgorithmVerificationLowerBound paperParams AlgorithmScheme.paperLimits (1 / 2) 1

OptimalOTS.Challenge.GenericLower.candidate :
  AlgorithmVerificationLowerBound paperParams AlgorithmScheme.paperLimits (1 / 2) 1

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

The generic lower challenge and one-half failure allowance are pinned independently of the
generic upper certificate. Its stricter `2^-128` availability requirement remains inside
the class covered by this lower theorem.

The separate [one-query argument](generic-one-query.md) is research toward 2, not a certificate.
Its normal form and transcript arguments have not yet been ported to Lean. No score of 2 is claimed.

## Local website

The generic lower card, chart and leaderboard show claim 1 as an ordinary Vitalik demo submission.
All three lower tracks and the generic upper track are open. The generic lower
row uses the checked claim with fictional attribution and no invented improvement. Its chart point,
detail page and solver profile link to the same persistent row. Website copy has no special baseline
labels. Existing Satoshi/Vitalik demo rows remain intact. Rules specify
the one-half lower signing-success threshold, the stricter upper allowance, and all four public
submission roots, without current scores.
The top navigation contains only the logo and Rules.
The rules keep scores out of the overview, illustrate cuts and shared hash origins, and preserve
the exact admissibility, encoding, DAG and submission requirements in expandable sections.

All 15 service tests pass, covering the generic lower queue and pull-request root mapping,
score-independent rules, framework isolation, Vitalik's linked generic submission and preservation of demo rows. A proof or admission
change must now update the website, metadata, rules and documentation in the same change.
Headless Firefox checks pass for the three lower lines and tables, generic lower's open status,
the simplified top navigation, direction switches, sorting, keyboard chart tooltips, filtered
deep links, rules expansion, and a narrow layout without page overflow.

## Official verification

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
