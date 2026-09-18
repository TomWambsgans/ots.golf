# ots.golf

How cheaply can a hash-based one-time signature be verified?

ots.golf compares **three lower-bound classes** and has two upper tracks: an **Upper bound** in
compressions for arbitrary oracle algorithms, and a **RISC-V upper bound** in cycles for
verified machine implementations. All five tracks are open. A submission is a Lean proof about a
pinned contract.
The public-key size is 128 bits, signatures fit in 5,504 bits, and security is 127 bits in the
contract's random-oracle experiment.

This is [ots.golf-dev](https://github.com/leanEthereum/ots.golf-dev), the core repository for the
model, verifier, website and reference certificates. Submit competition proof PRs to
[ots.golf-submissions](https://github.com/leanEthereum/ots.golf-submissions).
That repository contains the five submission roots and a pinned core submodule for local checking.

| Lower class | Admitted schemes | Checked lower bound |
|---|---|---:|
| Generality 3/3 | Arbitrary oracle programs with correctness, availability and resource guarantees | 1 |
| Generality 2/3 | Fixed DAGs, arbitrary deterministic functions and disclosure cuts | 18 |
| Generality 1/3 | Whole-word DAGs using 128-bit secrets, 256-bit hashes, fixed output halves and concatenation | 93 |

Each lower record applies to its class. The whole-word track retains its earlier
`disclosure-lower` identifier for URL and submission-root compatibility.

The **Upper bound** track (`generic-upper`) has a verified **106-compression construction**, with
perfect correctness, signing failure at most `2^-128`, 127-bit strong security, and the required
size and cost proofs. The **RISC-V upper bound** track (`riscv-upper`) has a verified
**24053-cycle RV64IM verifier** for a fixed-layout forest OTS: the machine's oracle computation is
proved equal to the Lean verifier on every input, every execution terminates, and accepting
executions cost at most 24053 cycles. The original DAG and historical partial-disclosure
upper certificates remain locally verifiable references.

## Model

All parties share one random oracle on bit strings. A new input gets an independent uniform
256-bit answer; equal inputs always receive the same answer across all uses. Every call costs
one compression per started 512-bit input block,
with a minimum of one. Computation and private randomness are free.

DAG signatures contain a 256-bit nonce and at most 5,248 bits of disclosed node values.
The message-and-nonce hash selects a cut; verification reconstructs the root and compares its
low 128 bits with the public key. Whole-word DAGs add only their operation restriction.
An algorithm scheme consists of three terminating oracle programs for key generation, signing
and verification, with an injective signature encoding.

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

Use `generic-lower` or `lower` for the other lower certificates, `generic-upper` for the
Upper bound construction, `riscv-upper` for the RISC-V implementation, and `upper` or
`disclosure-upper` for the historical references. macOS verification runs unsandboxed for trusted
local development. Hosted verification requires the Linux isolation described in
[the deployment guide](service/deploy/README.md).

For the website, run `uv sync --frozen` and `./run-local.sh` in `service/`.
The local preview loads the committed [Satoshi/Vitalik/Hal demo fixtures](service/demo/submissions.json)
by default, including on a fresh clone with no database.
See [service development](service/README.md)
and the [production review](docs/production-readiness.md) for checks and deployment gates.

To check a separate submissions checkout using this core's verifier, pass its path as `--source`,
for example `python3 verifier/verify.py generic-lower --source ../ots.golf-submissions`.
The verifier takes only that track's root; the contract and tooling come from this checkout.
See [repository setup](docs/repositories.md) for preparing the submissions workspace.

## Find the contract and proofs

- [Submission rules](AGENTS.md), [track metadata](challenges.json) and [verifier](verifier/verify.py).
- [DAG contract](formal/OptimalOTS/Statement.lean), [generic interface](formal/OptimalOTS/Algorithm.lean)
  and [whole-word restriction](formal/OptimalOTS/WholeWords.lean).
- [Generality 3/3 proof](docs/generic-lower.md), [Generality 2/3 proof](docs/lower-bound-proof.md)
  and [Generality 1/3 proof](docs/whole-words.md).
- [Upper bound proof](docs/generic-upper.md), [RISC-V track](docs/riscv-upper.md) and
  [contract audit](docs/AUDIT.md).
- `formal/Submissions/{GenericLower,Lower,DisclosureLower}/`: admitted lower roots.
- `formal/Submissions/GenericUpper/`: the admitted Upper bound root.
- `formal/Submissions/RiscvUpper/`: the admitted RISC-V upper bound root.
- `formal/Submissions/{Upper,DisclosureUpper}/`: historical upper references.
- `paper/`: the paper on the unrestricted DAG bound; `tools/`: numerical research tools.

The competition and chart were inspired by [better.codes](https://better.codes) and
[zk.golf](https://zk.golf). License: Apache 2.0.
