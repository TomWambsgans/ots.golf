# ots.golf service

The hosted verifier, the JSON API and the site, in one FastAPI app plus one worker process.

```sh
cd service
uv sync                                   # deps into .venv
.venv/bin/uvicorn app.main:app --reload --port 8000   # the site + API
.venv/bin/python -m app.worker            # the verifier (one submission at a time)
.venv/bin/python -m app.seed lower        # queue the lower baseline as the first submission
```

Prerequisites: `verifier/setup_tools.sh` has run and `formal/` has been built once (the worker
clones that warm build for every verification).

## Configuration (environment)

| Variable | Default | Meaning |
|---|---|---|
| `OTS_REPO_ROOT` | the parent of `service/` | the trusted checkout of the contract |
| `OTS_DATA_DIR` | `service/data` | database, logs, work directories |
| `OTS_DATABASE_URL` | `sqlite:///<data>/ots.db` | any SQLAlchemy URL (Postgres on the server) |
| `OTS_BASE_URL` | `http://localhost:8000` | public URL, used in links and OAuth |
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
webhook would.
