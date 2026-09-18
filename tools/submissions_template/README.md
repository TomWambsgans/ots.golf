# ots.golf submissions

Submit a Lean proof of a better verification bound by opening a pull request to
[leanEthereum/ots.golf-submissions](https://github.com/leanEthereum/ots.golf-submissions).
The model, verifier and website are developed in
[leanEthereum/ots.golf-dev](https://github.com/leanEthereum/ots.golf-dev).

| Track | Edit this directory | Better claim |
|---|---|---|
| Generality 3/3 lower | `formal/Submissions/GenericLower/` | Larger |
| Generality 2/3 lower | `formal/Submissions/Lower/` | Larger |
| Generality 1/3 lower | `formal/Submissions/DisclosureLower/` | Larger |
| Upper bound | `formal/Submissions/GenericUpper/` | Smaller |
| RISC-V upper bound | `formal/Submissions/RiscvUpper/` | Smaller |

Change only one directory per PR. Put the claim in `claim.txt` and export the required declarations
from `Solution.lean`. Follow the [submission rules](https://github.com/leanEthereum/ots.golf-dev/blob/{{CONTRACT_COMMIT}}/AGENTS.md), including import, file,
resource and axiom limits. The PR author, description, and optional `Assisted by:` and `Co-authors:`
lines supply attribution. A verified improvement becomes a record when that exact PR head is merged.

## Check your proof

Fork this repository, clone your fork with `--recurse-submodules`, and install elan and the
tool prerequisites in [setup_tools.sh](https://github.com/leanEthereum/ots.golf-dev/blob/{{CONTRACT_COMMIT}}/verifier/setup_tools.sh).
For an existing clone, run `git submodule update --init --recursive` first.

From this repository's root:

```sh
.contract/verifier/setup_tools.sh
(cd .contract/formal && lake exe cache get && lake build OptimalOTS)
python3 .contract/verifier/verify.py generic-lower --source .
```

Replace `generic-lower` with `lower`, `disclosure-lower`, `generic-upper` or `riscv-upper` as
appropriate.
The verifier reads your edited submission root and checks it against the trusted contract.
macOS verification is for trusted local development. Linux requires the bounded work storage
and isolation described in the [deployment guide](https://github.com/leanEthereum/ots.golf-dev/blob/{{CONTRACT_COMMIT}}/service/deploy/README.md).

## Contract pin

`.contract` is a Git submodule of the core repository, pinned to commit `{{CONTRACT_COMMIT}}`
(contract ID `{{CONTRACT_ID}}`). Maintainers update this pin when the competition contract changes.
Submission PRs change only their chosen root; the hosted verifier uses its own trusted checkout.

The initial roots contain checked reference certificates. Subsequent merged improvements live in
this repository; merging a submission does not modify the model or website in the core repository.

## Local website

The core submodule includes the website and the committed Satoshi/Vitalik demo fixtures.
After cloning with `--recurse-submodules`, start the preview with:

```sh
cd .contract/service
uv sync --frozen
./run-local.sh
```

Open `http://localhost:8000`. Startup populates a fresh database and preserves existing demo
rows on subsequent runs. Set `OTS_DEMO_DATA=0` to start without seeding the fictional entries.
The fixtures live with the website; checked submission proofs live in this repository.
