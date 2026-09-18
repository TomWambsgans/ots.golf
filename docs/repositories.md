# Core and submissions repositories

| Repository | Contents and role |
|---|---|
| [ots.golf-dev](https://github.com/leanEthereum/ots.golf-dev) | Trusted Lean model, challenge stubs, verifier, website, tooling and reference certificates |
| [ots.golf-submissions](https://github.com/leanEthereum/ots.golf-submissions) | The four public submission roots, proof PRs and merged records |

The local workspace contains both repositories:

```text
sig.golf/
├── ots.golf-dev/
└── ots.golf-submissions/
```

Run core commands from `ots.golf-dev/` and submission checks from `ots.golf-submissions/`.
Start localhost with `bash service/run-local.sh` from the core repository.

The submissions workspace has a `.contract` submodule pinned to a core commit for local proof
checking. Its PRs change one admitted root. The hosted verifier reads that root from the PR's exact
head, using its own core checkout for every protected file and verification tool.

Verification results are reported to the PR in the submissions repository. An improvement becomes
a record only when GitHub confirms that the verified head was merged there. The core's reference
certificates remain independently checked starting points; merging a proof never changes the model,
website, or trusted checkout. Repository identity is retained in each PR URL, so moving intake does
not send old result comments or merge events to an unrelated PR with the same number.

## Prepare the submissions repository

Commit and check the core changes, then run:

```sh
python3 tools/prepare_submissions_repo.py .build/ots.golf-submissions
```

The destination must be new. The command creates a local Git repository, copies only the four
admitted roots, adds the pinned core submodule, and stages the initial README, agent instructions
and submission PR template. Its `origin` points to `leanEthereum/ots.golf-submissions`.
It uses the local core checkout and does not contact GitHub or push anything.

Review and commit the prepared files. Publish the pinned core commit before publishing this
repository, so contributors can obtain the submodule. Contributors fork the submissions repository,
clone with `--recurse-submodules`, and follow its README for tool setup and local verification.

To update an existing competition contract, first deploy the reviewed core and then update the
submodule pin in a maintainer PR. Keep the workspace's checked reference or record roots compatible
with that contract. The preparation command never overwrites an existing repository or its records.

## Service configuration

```sh
OTS_CONTRACT_REPO=leanEthereum/ots.golf-dev
OTS_SUBMISSIONS_REPO=leanEthereum/ots.golf-submissions
```

`OTS_REPO_ROOT` remains the trusted core checkout. `OTS_CONTRACT_REPO` supplies links to that core;
`OTS_SUBMISSIONS_REPO` selects the only repository whose proof webhooks are accepted. Leaving the
latter unset keeps intake closed while localhost still links to the intended submissions repository.
Production requires both settings and separate repositories.

Install the Pull requests webhook on the submissions repository. The web process's fine-grained
GitHub token needs read access to contents and read/write access to commit statuses and pull requests
there. It needs no write permission on the core. Only maintainers update the trusted checkout.
See [deployment](../service/deploy/README.md) for credentials, isolation and launch checks.

For an existing installation, stop the worker, update the core Git remote, and set both variables
in the public environment file. Restart the web and worker only when the applicable launch checks
pass. Historical rows and outbox entries retain their original PR repository; they are never
silently reassigned to the new repository. The bootstrap script preserves existing environment files.
