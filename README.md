# ots.golf

How cheaply can a hash-based one-time signature be verified?

ots.golf compares **three lower-bound classes** and has two upper tracks: an **Upper bound** in
compressions for arbitrary oracle algorithms, and a **RISC-V upper bound** in cycles for
verified machine implementations. All five tracks are open. A submission is a Lean proof about a
pinned contract.
The public-key size is 128 bits, signatures fit in 5,376 bits, and security is 127 bits in the
contract's random-oracle experiment.

This is [ots.golf-dev](https://github.com/leanEthereum/ots.golf-dev), the core repository for the
model, verifier and website. Submit competition proof PRs to
[ots.golf-submissions](https://github.com/leanEthereum/ots.golf-submissions), which holds the
merged submission roots and a pinned core submodule for local checking. The core contains no proofs
of any track.

| Track | Slug | Admitted schemes | Reference proof |
|---|---|---|---:|
| Generality 1/3 lower | `lower-generality-1` | Whole-word DAGs using 128-bit secrets and constants, 256-bit hashes, fixed output halves and concatenation | 93 |
| Generality 2/3 lower | `lower-generality-2` | Fixed DAGs, arbitrary deterministic functions and disclosure cuts | 18 |
| Generality 3/3 lower | `lower-generality-3` | Admissible oracle algorithms | 1 |
| Upper bound | `upper-compressions` | Admissible oracle algorithms | 106 |
| RISC-V upper bound | `upper-riscv` | An admissible OTS with an RV64IM verifier proved equal to its Lean verifier | 1628 cycles |

- **Generality 1/3 lower** proves that every 127-bit secure whole-word DAG scheme has worst-case
  verification cost at least the claim, in compressions.
- **Generality 2/3 lower** proves the same bound for every 127-bit secure DAG scheme.
- **Generality 3/3 lower** proves it for every admissible, 127-bit secure oracle algorithm.
- **Upper bound** constructs an admissible, 127-bit secure scheme whose verification costs at most
  the claim in compressions on every input and oracle-answer path.
- **RISC-V upper bound** constructs such a scheme with a fixed RV64IM verifier proved equal to the
  Lean verifier, costing at most the claim in cycles on every execution.

The reference proofs are submitted as ordinary pull requests to the submissions repository.
The legacy DAG and whole-word upper tracks remain registered for local verification of their
reference proofs. [AGENTS.md](AGENTS.md) defines the exact requirements, exports and submission workflow.

## Model

All parties share one random oracle on bit strings. A new input gets an independent uniform
256-bit answer; equal inputs always receive the same answer across all uses. Every call costs
one compression per started 512-bit input block, with a minimum of one. Computation is free.
Key generation and signing may use private randomness; verification is deterministic.

DAG signatures contain a 128-bit nonce and at most 5,248 bits of disclosed node values.
The message-and-nonce hash selects a cut; verification reconstructs the root and compares its
low 128 bits with the public key. Whole-word DAGs add only their operation restriction.
An algorithm scheme consists of three terminating oracle programs for key generation, signing
and verification, with an injective signature encoding. It is admissible when it is perfectly
correct, verifies deterministically, fails to sign with probability at most `2^-128`, has
signatures of at most 5,376 bits and rejects longer ones, and stays within 1,024 key-generation
and `2^20` signing compressions on every path.

Every certificate uses strong unforgeability: any accepted pair other than the signed one counts,
and any accepted pair counts after a signing failure. Both count the cost of the
complete security experiment, including honest key generation, signing and final verification.

## Work locally

```sh
verifier/setup_tools.sh
cd formal
lake exe cache get
lake build OptimalOTS
lake env lean scripts/check-axioms.lean
cd ..
python3 verifier/verify.py lower-generality-1 --source ../ots.golf-submissions
```

`--source` is a submissions checkout; the verifier takes only that track's root, and the contract
and tooling come from this checkout. Use `lower-generality-3` or `lower-generality-2` for the other lower tracks,
`upper-compressions` for the Upper bound, `upper-riscv` for the RISC-V implementation, and `reference-generality-2` or
`reference-generality-1` for the historical references. macOS verification runs unsandboxed for trusted
local development. Hosted verification requires the Linux isolation described in
[the deployment guide](service/deploy/README.md).

For the website, run `uv sync --frozen` and `./run-local.sh` in `service/`.
The local preview loads the committed [demo fixtures](service/demo/README.md) by default,
including on a fresh clone with no database. See [service development](service/README.md) for
checks and [deployment](service/deploy/README.md) for launch gates.

See [repository setup](docs/repositories.md) for preparing the submissions workspace.

## Find the contract and proofs

- [Submission rules](AGENTS.md), [track metadata](challenges.json) and [verifier](verifier/verify.py).
- [DAG contract](formal/OptimalOTS/Dag.lean), [generic interface](formal/OptimalOTS/OracleAlgorithm.lean)
  and [whole-word restriction](formal/OptimalOTS/WholeWords.lean).
- [Generality 1/3 proof](docs/lower-generality-1.md), [Generality 2/3 proof](docs/lower-generality-2.md)
  and [Generality 3/3 proof](docs/lower-generality-3.md).
- [Upper bound proof](docs/upper-compressions.md), [RISC-V track](docs/upper-riscv.md),
  [contract audit](docs/AUDIT.md) and the [documentation index](docs/README.md).
- Submission roots (`formal/Submissions/<Root>/` in the submissions repository): `LowerGenerality3`,
  `LowerGenerality2`, `LowerGenerality1`, `UpperCompressions` and `UpperRiscv`; the legacy `ReferenceGenerality2` and
  `ReferenceGenerality1` references show that secure DAG and whole-word schemes exist.
- `paper/`: the paper on the unrestricted DAG bound; `tools/`: numerical research tools.

The competition and chart were inspired by [better.codes](https://better.codes) and
[zk.golf](https://zk.golf). License: Apache 2.0.
