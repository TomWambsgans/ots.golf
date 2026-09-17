# ots.golf

How cheap can verifying a hash-based one-time signature be? This repository is the contract, the
verifier, the baselines and the site of **[ots.golf](https://ots.golf)**, a competition on that number, modeled on
[better.codes](https://better.codes) (the Proximity Prize, by the Proximity Prize team, the Ethereum
Foundation, Yukon and zkSecurity; [proximity-prize/proximity-prize](https://github.com/proximity-prize/proximity-prize))
and [zk.golf](https://zk.golf) (zkSecurity; [zksecurity/zk-golf-challenges](https://github.com/zksecurity/zk-golf-challenges)).
The leaderboard and the progress chart follow better.codes' design.

The DAG model is a public computation graph of secret sources, deterministic nodes and hash nodes.
Signatures reveal node values selected by hashing the message with a nonce; the verifier recomputes
the root and compares its low 128 bits with the public key. Every party uses one random oracle on
bit strings. Repeated strings receive the same answer, even across node and index queries. The
contract provides no labels, tweaks or separation condition.

Hashing costs one compression per started 512-bit block of the actual input, at least one.
Deterministic computation and private randomness are free. The 512-bit message-and-nonce index
costs one compression. The upper baseline includes a 16-bit tweak in every node's input and pays
for it: chain inputs have 144 bits, three-digest inputs 400 bits, and the root input 912 bits.
With a 128-bit public key, signatures of at most 5504 bits and 127-bit security, the unrestricted
**DAG framework** has these baselines:

| Track | Certificate | Baseline | Record needs |
|---|---|---|---|
| Lower | `VerificationLowerBound paperParams c`, over weakly secure schemes | 18 (Lean-verified) | c ≥ record + 1 |
| Upper reference | a `Scheme paperParams`, `Secure`, every index ≤ c | 106 (Lean-verified) | Legacy certificate |

The verified lower bound 18 counts sets of hash nodes recomputed during verification. If every
signature cost at most 17, many indices would share such a set, allowing an attacker to convert
an observed signature and forge on a different message. The proof applies to every weakly secure
scheme, including schemes whose hash inputs coincide.

Unrestricted DAG bounds above 18 remain open. The former labeled-model bound 25 and the proposed fresh-weight
transfer do not establish a bare-oracle bound; see
[`docs/bare-oracle-port.md`](docs/bare-oracle-port.md) and the
[conditional numerical investigation](docs/bare-oracle-numerics.md).

Every ranked claim is a theorem about its pinned contract, checked by
the Lean kernel with [leanprover/comparator](https://github.com/leanprover/comparator).

A generic oracle-algorithm interface and an exact adapter for the 106-cost forest are available
as the [foundation for the single generic upper track](docs/generic-upper.md). Generic upper submissions
are not yet admitted: correctness and signing availability remain to be proved.

The **partial-disclosure framework** adds one restriction to the DAG model: a signature's payload may
derive from at most **46 distinct hash outputs**. Arbitrary fragments, deterministic mixtures and
Reed–Solomon encodings are allowed; multiple pieces of one digest count once. The 5248-bit payload,
256-bit nonce and 127-bit security requirements remain. Its `disclosure-lower` and `disclosure-upper`
certificates establish **80 and 106**; the latter is retained as a reference proof, while 80 is the
partial-disclosure lower baseline. See [the definition and proof status](docs/partial-disclosures.md).

The site has **three lower-bound frameworks and one fully generic upper track**. The chart compares
all three lower series and the single 106-cost generic adapter candidate. A [Lean-checked generic
lower bound of 1](docs/generic-lower.md) covers every correct, weakly secure algorithm whose signing
succeeds with probability at least one half. The `generic-lower` track is open, with a pinned
challenge and a normal submission root. The generic upper candidate awaits correctness and
availability proofs. Lower leaderboards
are grouped and filtered by framework. There are no separate DAG or partial-disclosure upper
leaderboards, and the public queue rejects new submissions to those legacy upper roots. Existing
proofs and historical pages remain available as references. Local demo lower records are explicitly
separate from the certified baselines.

## Layout

- `formal/` — the Lean project: `OptimalOTS/Statement.lean` (the contract), `OptimalOTS/Weak.lean`
  (strong security implies the weak security the lower track assumes), the challenge stubs, and
  `Submissions/{Lower,GenericLower,DisclosureLower}/` (lower submission roots) and
  `Submissions/{Upper,DisclosureUpper}/` (legacy upper reference roots).
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
