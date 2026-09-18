# Website and hosted verifier

The FastAPI website accepts pull requests and reports their results. A separate worker checks
proofs against the trusted checkout. The repository defines the contract; the website displays it.

## Local development

```sh
cd service
uv sync --frozen
./run-local.sh
```

Open `http://localhost:8000`. Startup refreshes the fictional Satoshi Nakamoto and Vitalik Buterin
submissions, preserving their IDs and dates. The page labels this as demo data. Claims follow the
contract through the offsets in `seed_demo.py`; generic lower has a zero-offset Vitalik submission.
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

The homepage has three lower frameworks: generic algorithms, DAGs and whole words. Their
leaderboards are independent. `/?framework=generic|dag|disclosure` filters the lower tables;
`#lower` and `#upper` select the direction. Scores appear as attributed submissions, without a
special baseline presentation. Rules explain the contract without current scores or proof history.

The only upper track is `generic-upper`, for fully generic algorithms. Its pinned construction
proves perfect correctness, signing failure at most 2⁻¹²⁸, 127-bit strong security, all size and
resource limits, and a worst-case verification cost of 106 compressions. It has its own records,
chart and leaderboard; the lower framework filter never filters upper submissions.
Legacy `upper` and `disclosure-upper` certificates remain accessible as historical references,
including their demo rows; they are not generic upper records. The latter belongs to Historical
partial disclosures, not Whole words. New public submissions to both legacy roots are rejected.
Default localhost demos preserve the existing 19 rows and add a fictional Vitalik submission at
the generic upper certificate's cost, followed by a fictional Satoshi improvement of one compression.
Both are marked as demos, without verified badges or commit links.

Whenever a certificate or admission status changes, update the metadata, charts, leaderboards,
rules and documentation together, then refresh and inspect localhost.

## Admission and records

A public pull request must change exactly one admitted submission root. The authenticated webhook
checks the repository, files and current head; the worker verifies that exact commit on the trusted
tree. A verified improvement becomes a record only after GitHub's API confirms that the verified
head was merged. Merges received before verification are remembered. The service never merges PRs.

The web process sends commit statuses and result comments from a durable outbox. A reporting outage
retries delivery without repeating the proof. Attribution comes from the PR author, optional
`Assisted by:` and `Co-authors:` lines, and the remaining description.

For local proof jobs, first prepare `verifier/setup_tools.sh` and the warm `formal/` build. Then
use `.venv/bin/python -m app.queue lower`, substituting `generic-lower`, `disclosure-lower` or `generic-upper` as
needed. `--baseline` initializes a checked certificate locally; it does not bypass verification.
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
| `OTS_CONTRACT_REPO` | empty | `owner/name`; required for public admission |
| `GITHUB_WEBHOOK_SECRET` | empty | webhook authentication; web process only |
| `GITHUB_TOKEN` | empty | GitHub API access and reporting; web process only |
| `OTS_MAX_INFLIGHT_PER_USER` | `2` | pending and verifying jobs per user |
| `OTS_QUEUE_CAP` | `20` | pending jobs overall |

Production web startup requires HTTPS, a repository, a token and a webhook secret of at least
32 characters. Production workers refuse GitHub credentials. Deploy the web and worker under
different Unix identities, sharing only the state group. See [deployment](deploy/README.md) for
storage, isolation, backups and mandatory launch checks. Local macOS verification is unsandboxed.

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
