# Documentation

Proof guides and reviews for ots.golf. The rules are on [ots.golf/rules](https://ots.golf/rules);
the precise submission specification is [AGENTS.md](../AGENTS.md). The proofs described here are
submission roots in the submissions repository, not in this core.

## Proof guides

| Guide | Track |
|---|---|
| [upper-compressions.md](upper-compressions.md) | Upper bound: the forest construction and its certificate |
| [upper-bound-proof.md](upper-bound-proof.md) | Upper bound: architecture of the forest's security proof |
| [nonce-128-analysis.md](nonce-128-analysis.md) | Upper bounds: the signing lemma and row potential behind the 128-bit nonce |
| [upper-riscv.md](upper-riscv.md) | RISC-V upper bound: machine ABI and certificate |
| [lower-generality-1.md](lower-generality-1.md) | Generality 1/3 lower bound: the whole-word class and its proof |
| [lower-generality-2.md](lower-generality-2.md) | Generality 2/3 lower bound: DAG schemes |
| [lower-generality-3.md](lower-generality-3.md) | Generality 3/3 lower bound: arbitrary oracle algorithms |

## Reviews and setup

- [AUDIT.md](AUDIT.md): audit of the contract semantics and trusted components.
- [repositories.md](repositories.md): the core and submissions repositories, and workspace preparation.

## Research and archive

- [research/](research/): open work toward larger lower bounds; not certificates.
- [archive/](archive/): superseded reports and analyses.
