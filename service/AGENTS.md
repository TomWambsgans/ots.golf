# Local preview

The user wants the invented Satoshi Nakamoto and Vitalik Buterin submissions present on localhost
by default. Preserve or restore those demo rows when updating the running local site. Do not
replace the demo board with a baseline-only board unless the user explicitly requests it.
Demo claims must follow the current contract baselines, using the offsets in `seed_demo.py`;
never preserve stale absolute claims when a baseline changes.

Always refresh localhost after committing. This checkout's Git `post-commit` hook runs
`refresh-local.sh`: it adjusts existing demo claims and triggers the running server to reload.
Verify the rendered homepage after a commit; do not push or deploy as part of a local refresh.

`./run-local.sh` seeds the demo board before starting the worker and web server; use this entry
point for local development. `OTS_DEMO_DATA=0` explicitly disables startup seeding.
`seed_demo.py` refuses nonlocal databases by default. Never force it against production.

If reseeding an already running site, wait for any active baseline verification to finish before
running `.venv/bin/python seed_demo.py`: the seed replaces baseline database rows.
For ordinary updates, `bash refresh-local.sh` preserves submission IDs and dates and leaves
real submissions alone, so it is safe while the worker is running.

The three frameworks apply only to lower bounds. The homepage plots three lower series, with
uncertified generic lower bounds in an explicitly pending lane outside the numeric axis. Never
substitute zero or a DAG theorem for a missing generic certificate. Lower leaderboards have separate
rankings for generic algorithms, DAGs and partial disclosures; `?framework=dag|disclosure|generic`
filters those lower tables only. Preserve `#lower` and `#upper` links.

There is exactly one upper track, for fully generic algorithms. Until generic admissibility is
proved and pinned, show the checked 106-cost adapter as a candidate, not an admitted record.
Do not relabel legacy DAG upper submissions as generic. The chart has one upper candidate line;
the upper leaderboard has no framework filter. Reject public submissions to legacy DAG upper roots.
Retain their proof files and historical pages as references, and preserve all existing demo rows.
The lower demo rows remain visible by default; legacy upper demos remain in historical solver pages.

Rules show certified lower baselines independently of the demo records. Partial-disclosure lower
uses `disclosure-lower` with the same baseline-relative demo offsets as DAG lower.
`seed_demo.py --refresh` preserves existing rows. Run isolated checks with
`.venv/bin/python -m unittest discover -s tests -v` from `service/` after changing this behavior.
