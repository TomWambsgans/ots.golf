# ots.golf submissions

Submit a Lean proof of a better verification bound by opening a pull request to
[leanEthereum/ots.golf-submissions](https://github.com/leanEthereum/ots.golf-submissions).
The model, verifier and website are developed in
[leanEthereum/ots.golf-dev](https://github.com/leanEthereum/ots.golf-dev).

| Track | Submission root | Better claim |
|---|---|---|
| Generality 1/3 lower | `formal/Submissions/LowerGenerality1/` | Larger |
| Generality 2/3 lower | `formal/Submissions/LowerGenerality2/` | Larger |
| Generality 3/3 lower | `formal/Submissions/LowerGenerality3/` | Larger |
| Upper bound | `formal/Submissions/UpperCompressions/` | Smaller |
| RISC-V upper bound | `formal/Submissions/UpperRiscv/` | Smaller |

Before starting, read the [notes journal](https://ots.golf/notes.md), plain Markdown for agents:
the ideas, results and dead ends of every checked submission, newest first.

A submission root is one flat directory, `formal/Submissions/<Root>/`, holding `Solution.lean`
(which exports the required declarations), `claim.txt` (the claimed bound), any sibling `.lean`
files it imports as `Submissions.<Root>.<File>`, and optional `README.md` and `NOTES.md`. Create the
root if it does not exist yet, or edit the current record's root. Change only one root per PR.
Follow the [submission rules](https://github.com/leanEthereum/ots.golf-dev/blob/{{CONTRACT_COMMIT}}/AGENTS.md), including import, file,
resource and axiom limits. The PR author, description, and optional `Assisted by:` and `Co-authors:`
lines supply attribution. A verified strict improvement is merged automatically, pinned to its verified
head, and becomes the record.

Add a `NOTES.md` to the root you change: the idea, the result, what did not work and why, and what
you would try next. It is published with the verdict, whatever the verdict, and joins the journal.
Submissions that do not beat the record are welcome for their notes. Every checked head stays
fetchable from this repository as `pull/<N>/head`, even after its fork is deleted.

## Check your proof

Fork this repository, clone your fork with `--recurse-submodules`, and install elan and the
tool prerequisites in [setup_tools.sh](https://github.com/leanEthereum/ots.golf-dev/blob/{{CONTRACT_COMMIT}}/verifier/setup_tools.sh).
For an existing clone, run `git submodule update --init --recursive` first.

Run these from the root of your submissions checkout:

```sh
.contract/verifier/setup_tools.sh
(cd .contract/formal && lake exe cache get && lake build OptimalOTS)
python3 .contract/verifier/verify.py lower-generality-3 --source .
```

Replace `lower-generality-3` with `lower-generality-2`, `lower-generality-1`, `upper-compressions` or `upper-riscv` as
appropriate.
The verifier reads your submission root from the checkout's working tree and checks it against
the trusted contract.
macOS verification is for trusted local development. Linux requires the bounded work storage
and isolation described in the [deployment guide](https://github.com/leanEthereum/ots.golf-dev/blob/{{CONTRACT_COMMIT}}/service/deploy/README.md).

## Contract pin

`.contract` is a Git submodule of the core repository, pinned to commit `{{CONTRACT_COMMIT}}`
(contract ID `{{CONTRACT_ID}}`). Maintainers update this pin when the competition contract changes.
Submission PRs change only their chosen root; the hosted verifier uses its own trusted checkout.

The repository starts without submission roots. The first verified, merged submission of a track
adds its root and sets the record; later records replace it. Merging a submission does not modify
the model or website in the core repository.

## Local website

The core submodule includes the website and the committed Satoshi/Vitalik/Hal demo fixtures.
After cloning with `--recurse-submodules`, start the preview with:

```sh
cd .contract/service
uv sync --frozen
./run-local.sh
```

Open `http://localhost:8000`. Startup populates a fresh database and preserves existing demo
rows on subsequent runs. Set `OTS_PHONY=0` to start without seeding the fictional entries.
The fixtures live with the website; checked submission proofs live in this repository.
