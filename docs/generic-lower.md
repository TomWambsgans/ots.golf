# A first lower bound for arbitrary oracle algorithms

Lean has checked the certificate below: a correct, available, weakly
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

The 1/2 failure allowance is deliberately weak. The theorem should cover every stricter allowance,
without selecting the final generic upper admission threshold. The interface's placeholder condition
that failure is merely less than one is insufficient for this argument: successful signing could
otherwise be far rarer than the security threshold.

This argument proves only one compression. A one-query verifier still depends on the secret oracle
table, so its accepting signatures cannot simply be selected by free public computation. A bound of
two or three requires another argument; it does not follow by repeating this proof.

## Checked certificate

```lean
OptimalOTS.GenericLower.candidate :
  AlgorithmVerificationLowerBound paperParams AlgorithmScheme.paperLimits (1 / 2) 1

OptimalOTS.GenericLower.paper_lowerBound_one {ε : ℝ≥0∞} (hε : ε ≤ 1 / 2) :
  AlgorithmVerificationLowerBound paperParams AlgorithmScheme.paperLimits ε 1
```

`AlgorithmVerificationLowerBound P L ε c` quantifies over every `AlgorithmScheme P`
satisfying `Admissible L ε` and `WeaklySecure`. It proves that every pathwise verification
budget is at least `c`. `AlgorithmScheme.Secure.weaklySecure` also checks in Lean, so the
result covers all strongly secure schemes meeting those admissibility requirements.

Files:

- `formal/OptimalOTS/AlgorithmWeak.lean`: weak experiment, strong-to-weak bridge, lower statement.
- `formal/OptimalOTS/AlgorithmZeroQuery.lean`: independence of zero-cost verification from the cache.
- `formal/OptimalOTS/AlgorithmLower.lean`: availability, public signature selection, fresh-message
  attack, experiment cost and success, and the numerical contradiction.

`lake build OptimalOTS.AlgorithmLower` and the complete `lake build OptimalOTS Submissions`
(8893 jobs) pass. The in-file axiom guard for `candidate` accepts
exactly `propext`, `Classical.choice` and `Quot.sound`. There are no admitted proofs or
`native_decide` calls. This is a checked foundation theorem, not yet a generic submission accepted
by the hosted comparator: the generic admission contract and availability threshold are not pinned.
The result works for every eventual threshold at most one half.

The separate [one-query argument](generic-one-query.md) is research toward 2, not a certificate.
Its normal form and transcript arguments have not yet been ported to Lean. No score of 2 is claimed.

## Local website

The generic lower card and chart now show the checked bound of 1 and its signing-success assumption.
Admission remains pending, and the theorem is not represented as an accepted solver submission.
The other lower leaderboards retain their baseline-relative demo rows. Rules were rewritten from
first principles, with no scores or candidate results.

All 13 service tests pass, including score-independent rules, numeric placement of the generic
foundation theorem, framework isolation and preservation of demo rows. Headless Firefox checks pass
for the three lower lines and single generic upper line, direction switches, sorting, keyboard
tooltips, filtered deep links, the DAG-format disclosure in the rules, and a narrow layout without
page overflow. Existing submission roots, contracts and verifier pins are unchanged.
