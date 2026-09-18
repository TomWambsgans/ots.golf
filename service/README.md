# Website and hosted verifier

The FastAPI website accepts pull requests and reports their results. A separate worker checks
proofs against the trusted `leanEthereum/ots.golf-dev` checkout. Proof PRs and merged records live
in `leanEthereum/ots.golf-submissions`; the core defines the contract and supplies the website.

## Local development

```sh
cd service
uv sync --frozen
./run-local.sh
```

Open `http://localhost:8000`. Startup refreshes the fictional Satoshi Nakamoto and Vitalik Buterin
submissions, preserving their IDs and dates. The page labels this as demo data. Claims follow the
contract through the offsets in the committed [demo fixtures](demo/submissions.json); generic lower
has a zero-offset Vitalik submission. A fresh clone recreates the board without a database dump.
Real submissions are left alone. Set `OTS_DEMO_DATA=0` to skip this refresh.

After every local commit, refresh localhost and check the rendered page. This checkout's
`post-commit` hook runs `service/refresh-local.sh`, which refreshes demo claims and reloads the
web process, including its cached commit. Install the hook in another checkout with:

```sh
install -m 755 service/post-commit "$(git rev-parse --git-path hooks/post-commit)"
```

Run that command from the repository root. For a manual refresh, use
`bash service/refresh-local.sh`. Restart `run-local.sh` after changing worker code: the worker does
not hot-reload. The startup script removes GitHub credentials from the worker's environment.

`seed_demo.py --remove` removes fictional rows. Plain `seed_demo.py` replaces them and removes
local certificate initialization rows; use `--refresh` for routine updates. The script refuses
production mode and non-loopback site URLs, even with `--force`, and normally accepts only the
default local database. Do not use fictional data in production.

## Tracks and presentation

The homepage has three lower frameworks: Generality 3/3 (any algorithm), 2/3 (DAGs with arbitrary
functions) and 1/3 (whole-word DAGs). Each has its own leaderboard.
`/?framework=generic|dag|disclosure` filters the lower tables; `#lower` and `#upper` select the
direction. Scores appear as attributed submissions. Rules define the contract's requirements.

The Upper bound track (`generic-upper`) accepts any oracle algorithm. Its pinned construction
proves perfect correctness, signing failure at most 2⁻¹²⁸, 127-bit strong security, all size and
resource limits, and a worst-case verification cost of 106 compressions. It has its own records,
chart and leaderboard. The RISC-V upper bound track (`riscv-upper`) scores a verified RV64IM
verifier by its proved accepting-execution cycle bound; its pinned certificate costs 229113 virtual
cycles. It has its own card, leaderboard and chart with an independent cycle axis, never combined
with compression bounds. The framework filter applies to lower submissions.
Legacy `upper` and `disclosure-upper` certificates and demos remain accessible under Historical
DAG and Historical partial disclosures. Public admission to those roots is closed.
Default localhost demos preserve the existing 19 rows and add a fictional Vitalik submission at
the generic upper certificate's cost, followed by a fictional Satoshi improvement of one compression.
Both carry demo labels and unverified status. A further fictional Satoshi row shows the RISC-V
certificate's own cost with zero improvement.

Whenever a certificate or admission status changes, update the metadata, charts, leaderboards,
rules and documentation together, then refresh and inspect localhost.

## Admission and records

A public pull request to the submissions repository must change exactly one admitted submission root. The authenticated webhook
checks the repository, files and current head; the worker verifies that exact commit on the trusted
tree. A verified improvement becomes a record only after GitHub's API confirms that the verified
head was merged. Merges received before verification are remembered. The service never merges PRs.
The trusted core checkout remains independent of submission merges. Historical result reports
retain the PR's repository and are never redirected to the same PR number in another repository.

The web process sends commit statuses and result comments from a durable outbox. A reporting outage
retries delivery without repeating the proof. Attribution comes from the PR author, optional
`Assisted by:` and `Co-authors:` lines, and the remaining description.

For local proof jobs, first prepare `verifier/setup_tools.sh` and the warm `formal/` build. Then
use `.venv/bin/python -m app.queue lower`, substituting `generic-lower`, `disclosure-lower`,
`generic-upper` or `riscv-upper` as needed. `--baseline` queues a certificate for verification and local initialization.
The two legacy upper slugs also work for local reference checks. Only one worker may use a data
directory; lock files enforce this across processes on the same host.

## Configuration

| Variable | Default | Purpose |
|---|---|---|
| `OTS_ENV` | `development` | `development` or `production` |
| `OTS_ROLE` | `web` | `web` or `worker` |
| `OTS_REPO_ROOT` | checkout root | trusted contract checkout |
| `OTS_DATA_DIR` | `service/data` | SQLite database, logs and process locks |
| `OTS_WORK_DIR` | `<data>/work` | disposable verification jobs; dedicated bounded mount on Linux |
| `OTS_DATABASE_URL` | `sqlite:///<data>/ots.db` | database connection; deployment uses SQLite |
| `OTS_BASE_URL` | `http://localhost:8000` | site origin, without a path |
| `OTS_CONTRACT_REPO` | `leanEthereum/ots.golf-dev` | core repository; source and specification links |
| `OTS_SUBMISSIONS_REPO` | empty | proof PR repository; set to `leanEthereum/ots.golf-submissions` to configure intake |
| `GITHUB_WEBHOOK_SECRET` | empty | webhook authentication; web process only |
| `GITHUB_TOKEN` | empty | GitHub API access and reporting; web process only |
| `OTS_MAX_INFLIGHT_PER_USER` | `2` | pending and verifying jobs per user |
| `OTS_QUEUE_CAP` | `20` | pending jobs overall |

Production web startup requires HTTPS, two distinct repositories, a token and a webhook secret of at least
32 characters. Production workers refuse GitHub credentials. Deploy the web and worker under
different Unix identities, sharing only the state group. See [deployment](deploy/README.md) for
storage, isolation, backups and mandatory launch checks. Local macOS verification is unsandboxed.
See [repository setup](../docs/repositories.md) for preparing the separate submissions workspace.

## Checks

```sh
.venv/bin/python -m unittest discover -s tests -v
cd ..
python3 service/browser_check.py --output-dir /tmp/ots-ui
python3 tools/check_repo.py --numerics-python .venv-tools/bin/python --formal --paper
```

Service tests use isolated databases. The optional browser check uses Firefox against the seeded
localhost preview and exercises desktop/mobile layouts, both color schemes, keyboard controls,
filters, tooltips, reduced motion and error pages. See [numerical tool setup](../tools/README.md)
for NumPy and the repository runner; add `--official` to run all six certificate pipelines.
The [production review](../docs/production-readiness.md) records results and remaining launch gates.
