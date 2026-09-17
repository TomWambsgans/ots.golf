# ots.golf

How cheap can verifying a hash-based one-time signature be? This repository is the contract, the
verifier, the baselines and the site of **[ots.golf](https://ots.golf)**, a competition on that number, modeled on
[better.codes](https://better.codes) (the Proximity Prize, by the Proximity Prize team, the Ethereum
Foundation, Yukon and zkSecurity; [proximity-prize/proximity-prize](https://github.com/proximity-prize/proximity-prize))
and [zk.golf](https://zk.golf) (zkSecurity; [zksecurity/zk-golf-challenges](https://github.com/zksecurity/zk-golf-challenges)).
The leaderboard and the progress chart follow better.codes' design.

The model is the one of *A Verification Lower Bound for Hash-Based One-Time Signatures*
(`paper/`): a public computation graph of secret sources, deterministic nodes and hash nodes;
signatures reveal node values selected by hashing the message with a nonce; the verifier
recomputes the root and compares a 128-bit prefix with the public key. Hashing is charged one compression
per started 512-bit block of the input and nothing else: a per-key public parameter can be absorbed
once in a block of its own and its chaining state reused (an observation of Justin Drake), and
tweaks are the role of the model's labels. A chain hash and the message index cost one compression each. With a 128-bit public key, signatures of at most 5504 bits and 127-bit security:

| Track | Certificate | Baseline | Record needs |
|---|---|---|---|
| Lower | `VerificationLowerBound paperParams c`, over weakly secure schemes | 25 (Lean-verified) | c ≥ record + 1 |
| Upper | a `Scheme paperParams`, `Secure`, every index ≤ c | 106 (Lean-verified) | c ≤ record − 1 |

Every ranked claim is a theorem about the pinned `formal/OptimalOTS/Statement.lean`, checked by
the Lean kernel with [leanprover/comparator](https://github.com/leanprover/comparator).

## Layout

- `formal/` — the Lean project: `OptimalOTS/Statement.lean` (the contract), `OptimalOTS/Weak.lean`
  (strong security implies the weak security the lower track assumes), the challenge stubs, and
  `Submissions/{Lower,Upper}/` (the submission roots, holding the baselines).
- `verifier/` — the policy checks, the contract pin, the comparator configs, the local verifier.
- `challenges.json` — tracks, limits, protected files. `AGENTS.md` — the rules. `llms.txt` — for
  scripts and agents.
- `service/` — the site and the hosted verifier (`service/README.md`; deployment in `service/deploy/`).
- `paper/` — the paper. `docs/` — the proof maps of both baselines and the statement audit.
- `tools/` — the searches behind the two baselines: forest shapes and the lower bound's operating point.

## Build and verify locally

```sh
verifier/setup_tools.sh                        # comparator + lean4export on this toolchain
cd formal && lake exe cache get && lake build OptimalOTS Submissions   # Mathlib, VCVio, contract, baselines
cd .. && python3 verifier/verify.py lower --source .
```

See `AGENTS.md` for the rules. License: Apache 2.0.
