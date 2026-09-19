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

Open `http://localhost:8000`. Startup refreshes the fictional [demo fixtures](demo/README.md),
preserving their IDs and dates; each row carries a demo label. A fresh clone recreates the board
without a database dump. Real submissions are left alone. Set `OTS_PHONY=0` to skip this refresh
and show real submissions only: a track without a merged record shows "No record yet".

After every local commit, refresh localhost and check the rendered page. This checkout's
`post-commit` hook runs `service/refresh-local.sh`, which re-seeds the demo rows and reloads the
web process, including its cached commit. Install the hook in another checkout with:

```sh
install -m 755 service/post-commit "$(git rev-parse --git-path hooks/post-commit)"
```

Run that command from the repository root. For a manual refresh, use
`bash service/refresh-local.sh`. Restart `run-local.sh` after changing worker code: the worker does
not hot-reload. The startup script removes GitHub credentials from the worker's environment.

`seed_demo.py --remove` removes fictional rows. Plain `seed_demo.py` replaces them; use `--refresh`
for routine updates. The script refuses
production mode and non-loopback site URLs, even with `--force`, and normally accepts only the
default local database. Do not use fictional data in production.

## Presentation

The homepage has three lower frameworks, each with its own leaderboard, and two upper tracks.
`/?framework=generality-1|generality-2|generality-3` filters the lower tables only; `#lower` and `#upper` select
the direction. Scores appear as attributed submissions; rules define the contract's requirements
without scores. The RISC-V upper track has its own card, leaderboard and chart with an
independent cycle axis, never combined with compression bounds. The two witnesses have no demo rows and no leaderboard.

The database is a disposable cache: the website rebuilds it from GitHub at startup
(`app.resync`), so an empty data directory comes back as before; see
[deployment](deploy/README.md#rebuilding-the-server-from-nothing).

Whenever the contract or an admission status changes, update the metadata, charts, leaderboards,
rules and documentation together, then refresh and inspect localhost.

## Admission and records

A public pull request to the submissions repository must change exactly one admitted submission root. The authenticated webhook
checks the repository, files and current head; the worker verifies that exact commit on the trusted
tree. A verified strict improvement is merged automatically by the web process, pinned to the
verified head (GitHub refuses if the head moved), and becomes the record; `OTS_AUTO_MERGE=0` turns
this off, leaving merges to maintainers. A track has no record until its first verified, merged
submission, which becomes the record whatever its claim. Merges received before verification are
remembered. Record decisions ignore demo rows.
The trusted core checkout remains independent of submission merges. Historical result reports
retain the PR's repository and are never redirected to the same PR number in another repository.

The web process sends commit statuses and result comments from a durable outbox. A reporting outage
retries delivery without repeating the proof. Attribution comes from the PR author, optional
`Assisted by:` and `Co-authors:` lines, and the remaining description.

For local proof jobs, first prepare `verifier/setup_tools.sh` and the warm `formal/` build. Then
use `.venv/bin/python -m app.queue lower --repo ../../ots.golf-submissions`, substituting
`lower-generality-3`, `lower-generality-1`, `upper-compressions` or `upper-riscv` as needed; `--repo` is a
submissions checkout. Local jobs never become records. The two legacy upper slugs also work for
local reference checks. Only one worker may use a data
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
| `OTS_AUTO_MERGE` | `1` | merge a verified record-breaking PR automatically; needs contents write |
| `OTS_PHONY` | `1` | re-seed the invented demo rows at every start; `0` shows real submissions only |
| `OTS_RESYNC_ON_START` | `1` | rebuild missing submissions from GitHub when the website starts |
| `OTS_BOT_LOGIN` | token's login | account whose PR comments carry verdicts |
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
for NumPy and the repository runner; add `--official --submissions PATH` to verify every submission
root in a submissions checkout.
[Deployment](deploy/README.md) lists the remaining launch gates.
