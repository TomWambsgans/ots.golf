# ots.golf

How cheaply can a hash-based one-time signature be verified?

ots.golf compares **three lower-bound classes** and admits upper constructions through a
**single generic algorithm interface**. A submission is a Lean proof about a pinned contract.
The public-key size is 128 bits, signatures fit in 5,504 bits, and security is 127 bits in the
contract's random-oracle experiment.

| Lower framework | Admitted schemes | Checked lower bound |
|---|---|---:|
| Generic algorithms | Arbitrary oracle programs with correctness, availability and resource guarantees | 1 |
| DAGs | Fixed computation graphs, arbitrary deterministic operations and disclosure cuts | 18 |
| Whole words | DAGs using 128-bit secrets, 256-bit hashes, fixed output halves and concatenation | 93 |

These bounds apply to different classes. The whole-word result does not establish 93 for
arbitrary DAGs or generic algorithms. The whole-word track retains its earlier
`disclosure-lower` identifier for URL and submission-root compatibility.

The generic upper interface has a checked **106-compression candidate** with security, size
and cost proofs. Its correctness and signing-availability proofs are still required before
upper submissions open. The original DAG and historical partial-disclosure upper certificates
remain locally verifiable references; neither is an admitted generic upper record.

## Model

All parties share one random oracle on bit strings. A new input gets an independent uniform
256-bit answer; equal inputs always receive the same answer. There are no implicit labels,
tweaks or domain separation. Every call costs one compression per started 512-bit input block,
with a minimum of one. Computation and private randomness are free.

DAG signatures contain a 256-bit nonce and at most 5,248 bits of disclosed node values.
The message-and-nonce hash selects a cut; verification reconstructs the root and compares its
low 128 bits with the public key. Whole-word DAGs add only their operation restriction.
Generic algorithms have no mandatory graph, nonce or disclosure pattern.

The lower certificates cover weak unforgeability: a forgery must use a new message, or signing
must have failed. Upper certificates require strong unforgeability. Both count the cost of the
complete security experiment, including honest key generation, signing and final verification.

## Work locally

```sh
verifier/setup_tools.sh
cd formal
lake exe cache get
lake build OptimalOTS Submissions
lake env lean scripts/check-axioms.lean
cd ..
python3 verifier/verify.py disclosure-lower --source .
```

Use `generic-lower` or `lower` for the other lower certificates, and `upper` or
`disclosure-upper` for the historical references. macOS verification checks proofs but does
not sandbox untrusted code. Hosted verification requires the Linux isolation described in
[the deployment guide](service/deploy/README.md).

For the website, run `uv sync --frozen` and `./run-local.sh` in `service/`.
The local preview includes clearly marked fictional Satoshi/Vitalik submissions by default;
these are separate from the checked results above. See [service development](service/README.md)
and the [production review](docs/production-readiness.md) for checks and deployment gates.

## Find the contract and proofs

- [Submission rules](AGENTS.md), [track metadata](challenges.json) and [verifier](verifier/verify.py).
- [DAG contract](formal/OptimalOTS/Statement.lean), [generic interface](formal/OptimalOTS/Algorithm.lean)
  and [whole-word restriction](formal/OptimalOTS/WholeWords.lean).
- [Generic lower proof](docs/generic-lower.md), [DAG lower proof](docs/lower-bound-proof.md)
  and [whole-word lower proof](docs/whole-words.md).
- [Generic upper status](docs/generic-upper.md) and [contract audit](docs/AUDIT.md).
- `formal/Submissions/{GenericLower,Lower,DisclosureLower}/`: admitted lower roots.
- `formal/Submissions/{Upper,DisclosureUpper}/`: historical upper references.
- `paper/`: the paper on the unrestricted DAG bound; `tools/`: numerical research tools.

The competition and chart were inspired by [better.codes](https://better.codes) and
[zk.golf](https://zk.golf). License: Apache 2.0.
