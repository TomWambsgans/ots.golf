# ots.golf

How cheap can verifying a hash-based one-time signature be? This repository is the contract, the
verifier and the baselines of **ots.golf**, a competition on that number, modeled on
[better.codes](https://better.codes) (the Proximity Prize, by the Proximity Prize team, the Ethereum
Foundation, Yukon and zkSecurity; [proximity-prize/proximity-prize](https://github.com/proximity-prize/proximity-prize))
and [zk.golf](https://zk.golf) (zkSecurity; [zksecurity/zk-golf-challenges](https://github.com/zksecurity/zk-golf-challenges)).
The leaderboard and the progress chart follow better.codes' design.

The model is the one of *A Verification Lower Bound for Hash-Based One-Time Signatures*
(`paper/`): a public computation graph of secret sources, deterministic nodes and hash nodes;
signatures reveal node values selected by hashing the message with a nonce; the verifier
recomputes the root and compares a 128-bit prefix with the public key. Hashing is charged one unit
per started 512-bit block of the input plus 192 overhead bits (a 128-bit public parameter for
multi-user domain separation and a 64-bit tweak), so a chain hash costs one unit and the message
index two. With a 128-bit public key, signatures of at most 5504 bits and 127-bit security:

| Track | Certificate | Baseline | Record needs |
|---|---|---|---|
| Lower | `VerificationLowerBound paperParams c` | 25 (Lean-verified) | c ≥ record + 1 |
| Upper | a `Scheme paperParams`, `Secure`, every index ≤ c | 109 (Lean-verified) | c ≤ record − 1 |

Every ranked claim is a theorem about the pinned `formal/OptimalOTS/Statement.lean`, checked by
the Lean kernel with [leanprover/comparator](https://github.com/leanprover/comparator).

## Layout

- `formal/` — the Lean project: `OptimalOTS/Statement.lean` (the contract), the challenge stubs,
  and `Submissions/{Lower,Upper}/` (the submission roots, holding the baselines).
- `verifier/` — the policy checks, the contract pin, the comparator configs, the local verifier.
- `challenges.json` — tracks, limits, protected files. `AGENTS.md` — the rules. `llms.txt` — for
  scripts and agents.
- `paper/` — the paper. `docs/` — the proof maps of both baselines and the statement audit.

## Build and verify locally

```sh
verifier/setup_tools.sh                        # comparator + lean4export on this toolchain
cd formal && lake exe cache get && lake build   # Mathlib, VCVio, contract, baselines
cd .. && python3 verifier/verify.py lower --source .
```

See `AGENTS.md` for the rules and `PLAN.md` for the roadmap. License: Apache 2.0.
