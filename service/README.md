# ots.golf service

The hosted verifier and the site, in one FastAPI app plus one worker process. The repository is
the source of truth; the site is its human-readable view.

```sh
cd service
uv sync                                   # deps into .venv
./run-local.sh                            # demo board, site, webhook and verifier worker
```

`./run-local.sh` starts the site and the worker together and, by default, seeds the local preview
with the invented Satoshi Nakamoto and Vitalik Buterin submissions. Preserve this demo board when
refreshing localhost; it is the preferred development view. Seeding is repeatable: it replaces
earlier demo rows and removes baseline entries from the preview board.
Claims are improvements relative to `challenges.json`: with baselines 18 and 106, the demo
records progress from 19 to 20 and from 105 to 101.
Partial-disclosure tracks have their own demo rows, with the same offsets from their own baselines.
The homepage compares three **lower-bound** frameworks in cards and a shared chart. DAG and
partial-disclosure lower bounds have numeric records. Generic lower shows the checked foundation
theorem at 1, assuming correct signing succeeds at least half the time; generic admission remains
pending. The leaderboard defaults to all lower frameworks, grouped by class.
Filter it with `/?framework=dag`, `/?framework=disclosure`, or `/?framework=generic`.

There is one **upper** track: fully generic algorithms. Its checked 106-cost adapter is shown as a
candidate while correctness, signing availability and the generic challenge remain unfinished.
There are no separate DAG or partial-disclosure upper leaderboards. `#lower` and `#upper` select
the direction; framework filters apply only to lower bounds. Legacy DAG upper histories remain
accessible as reference pages, and their demo rows are preserved, without becoming generic records.
The public queue rejects new submissions to legacy upper roots. Rules describe the requirements
without scores, candidate results or leaderboard history.

After each local commit, the installed Git `post-commit` hook runs `refresh-local.sh` to adjust
demo claims to the current baselines and reload the running site, including its cached commit.
It preserves submission links and dates, adds demo rows for newly introduced tracks, and leaves real
submissions and baseline rows untouched. To install this hook in another checkout, run from the
repository root: `install -m 755 service/post-commit "$(git rev-parse --git-path hooks/post-commit)"`.
The same refresh can be run manually with `bash service/refresh-local.sh` from the repository root.

Use `OTS_DEMO_DATA=0 ./run-local.sh` to skip seeding. To also remove existing demo rows, run
`.venv/bin/python seed_demo.py --remove` first. `seed_demo.py` only accepts the default local
database unless explicitly forced; the deployed services do not run the local startup script.

Prerequisites: `verifier/setup_tools.sh` has run and `formal/` has been built once (the worker
clones that warm build for every verification).

## Configuration (environment)

| Variable | Default | Meaning |
|---|---|---|
| `OTS_REPO_ROOT` | the parent of `service/` | the trusted checkout of the contract |
| `OTS_DATA_DIR` | `service/data` | database, logs, work directories |
| `OTS_DATABASE_URL` | `sqlite:///<data>/ots.db` | any SQLAlchemy URL; SQLite by default, also on the server |
| `OTS_BASE_URL` | `http://localhost:8000` | public URL, used in links |
| `GITHUB_WEBHOOK_SECRET` | | verifies `/webhooks/github` |
| `GITHUB_TOKEN` | | posts commit statuses and PR comments |
| `OTS_CONTRACT_REPO` | | `owner/name` of the public contract repository |
| `OTS_MAX_INFLIGHT_PER_USER` | `2` | pending + verifying per user |
| `OTS_QUEUE_CAP` | `20` | pending overall |

## The one way in

A pull request against the contract repository that changes exactly one submission root. The
webhook queues its head commit; the worker fetches it, keeps only the submission root, verifies
it on the trusted tree with `verifier/verify.py`, and reports back as a commit status and a
comment. Verified and strictly better than the record: merge it, the merge is the promotion.

Attribution comes from the pull request: the author, plus optional `Assisted by: <model>` and
`Co-authors: a, b` lines in its body; the rest of the body is the description.

On localhost there is no GitHub, so `python -m app.queue` queues a local commit the way the
webhook would. For a baseline-only preview with demo data disabled, use
`.venv/bin/python -m app.queue lower --baseline` (and the same command for `upper`).
The admitted partial-disclosure slug is `disclosure-lower`. The legacy `upper` and
`disclosure-upper` slugs remain available for local reference verification, not public upper admission.

Run the framework and demo-preservation checks with
`.venv/bin/python -m unittest discover -s tests -v`. They use an isolated SQLite database.
