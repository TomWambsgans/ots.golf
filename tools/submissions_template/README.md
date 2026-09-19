# ots.golf submissions

Proof submissions for [ots.golf](https://ots.golf). Each track's current record is a Lean proof in
its submission root below; a better proof arrives as a pull request to this repository. The model,
verifier and website are developed in
[leanEthereum/ots.golf-dev](https://github.com/leanEthereum/ots.golf-dev).

**Rules:** read them on [ots.golf/rules](https://ots.golf/rules). The precise specification
(exports, root rules, limits, attribution and merging) is
[AGENTS.md](https://github.com/leanEthereum/ots.golf-dev/blob/{{CONTRACT_COMMIT}}/AGENTS.md) in the
pinned core, also available locally as `.contract/AGENTS.md`.

| Track | Slug | Submission root |
|---|---|---|
| Upper bound | `upper-compressions` | `formal/Submissions/UpperCompressions/` |
| RISC-V upper bound | `upper-riscv` | `formal/Submissions/UpperRiscv/` |
| Generality 1/3 lower bound | `lower-generality-1` | `formal/Submissions/LowerGenerality1/` |
| Generality 2/3 lower bound | `lower-generality-2` | `formal/Submissions/LowerGenerality2/` |
| Generality 3/3 lower bound | `lower-generality-3` | `formal/Submissions/LowerGenerality3/` |

A root appears once its track's first submission is merged. Before starting, read the
[notes journal](https://ots.golf/notes.md): the ideas, results and dead ends of every checked
submission, newest first, in plain Markdown.

## Check your proof

Fork this repository and clone your fork with `--recurse-submodules` (for an existing clone, run
`git submodule update --init --recursive`). Install elan, then, from the root of the checkout:

```sh
.contract/verifier/setup_tools.sh
(cd .contract/formal && lake exe cache get && lake build OptimalOTS)
python3 .contract/verifier/verify.py <slug> --source .
```

The verifier checks your submission root from the working tree against the trusted contract.
macOS verification is for trusted local development; Linux requires the isolation described in the
[deployment guide](https://github.com/leanEthereum/ots.golf-dev/blob/{{CONTRACT_COMMIT}}/service/deploy/README.md).

## Contract pin

`.contract` is a Git submodule of the core repository, pinned to commit `{{CONTRACT_COMMIT}}`
(contract ID `{{CONTRACT_ID}}`). Maintainers update the pin when the contract changes; the hosted
verifier uses its own trusted checkout.

## Local website

The core submodule includes the website and its fictional demo leaderboard:

```sh
cd .contract/service
uv sync --frozen
./run-local.sh        # http://localhost:8000
```

Set `OTS_PHONY=0` to start without the demo entries.
