# ots.golf

How cheap can verifying a hash-based one-time signature be? This repository is the contract, the
verifier and the baselines of **ots.golf**, a competition on that number, modeled on
[better.codes](https://better.codes) and [zk.golf](https://zk.golf).

The model is the one of *A Verification Lower Bound for Hash-Based One-Time Signatures*
(`paper/`): a public computation graph of secret sources, deterministic nodes and hash nodes;
signatures reveal node values selected by hashing the message with a nonce; the verifier
recomputes the root and compares a 128-bit prefix with the public key. Hashing is charged one unit
per started 512-bit block. With a 128-bit public key, signatures of at most 5504 bits and 127-bit
security:

| Track | Certificate | Baseline | Record needs |
|---|---|---|---|
| Lower | `VerificationLowerBound paperParams c` | 25 (Lean-verified) | c ≥ record + 1 |
| Upper | a `Scheme paperParams`, `Secure`, every index ≤ c | 106 (paper; Lean proof pending) | c ≤ record − 1 |

Every ranked claim is a theorem about the pinned `formal/OptimalOTS/Statement.lean`, checked by
the Lean kernel with [leanprover/comparator](https://github.com/leanprover/comparator).

## Layout

- `formal/` — the Lean project: `OptimalOTS/Statement.lean` (the contract), the challenge stubs,
  and `Submissions/{Lower,Upper}/` (the submission roots, holding the baselines).
- `verifier/` — the policy checks, the contract pin, the comparator configs, the local verifier.
- `challenges.json` — tracks, limits, protected files. `AGENTS.md` — the rules. `llms.txt` — for
  scripts and agents.
- `paper/` — the paper. `docs/` — the lower-bound proof map and the statement audit.

## Build and verify locally

```sh
verifier/setup_tools.sh                        # comparator + lean4export on this toolchain
cd formal && lake exe cache get && lake build   # Mathlib, VCVio, contract, baselines
cd .. && python3 verifier/verify.py lower --source .
```

See `AGENTS.md` for the rules and `PLAN.md` for the roadmap. License: Apache 2.0.
