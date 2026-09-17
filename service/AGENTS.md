# Local preview

The user wants the invented Satoshi Nakamoto and Vitalik Buterin submissions present on localhost
by default. Preserve or restore those demo rows when updating the running local site. Do not
replace the demo board with a baseline-only board unless the user explicitly requests it.
Demo claims must follow the current contract baselines, using the offsets in `seed_demo.py`;
never preserve stale absolute claims when a baseline changes.
Show results as ordinary submissions with solver attribution, never as a special "baseline" in
the website. Generic lower's checked claim appears as a default Vitalik demo submission with zero
offset from the contract claim. Preserve it across refreshes, including its ID and dates, and keep
its demo label. Internal verifier thresholds still come from the contract.

Always refresh localhost after committing. This checkout's Git `post-commit` hook runs
`refresh-local.sh`: it adjusts existing demo claims and triggers the running server to reload.
Verify the rendered homepage after a commit; do not push or deploy as part of a local refresh.
Always synchronize the site's admission status, baseline metadata, chart, leaderboards and rules
whenever a proof or contract status changes. Refresh localhost and check the rendered pages as part
of the same change; do not wait for a separate request to update the website.

`./run-local.sh` seeds the demo board before starting the worker and web server; use this entry
point for local development. `OTS_DEMO_DATA=0` explicitly disables startup seeding.
`seed_demo.py` refuses nonlocal databases by default. Never force it against production.

If reseeding an already running site, wait for any active baseline verification to finish before
running `.venv/bin/python seed_demo.py`: the seed replaces baseline database rows.
For ordinary updates, `bash refresh-local.sh` preserves submission IDs and dates and leaves
real submissions alone, so it is safe while the worker is running.

The three frameworks apply only to lower bounds. All three lower tracks are open, and the homepage
plots three certified lower series from their normal `challenges.json` metadata. Generic lower uses
`generic-lower`, with baseline 1 and the fixed assumption that correct signing succeeds at least
half the time for every public-key-dependent message selection. Do not hardcode a separate generic
foundation certificate or show lower admission as pending. If a future framework has no checked
certificate, use a pending lane outside the numeric axis. Never substitute zero or a DAG theorem
for a missing generic certificate. Lower leaderboards have separate
rankings for generic algorithms, DAGs and partial disclosures; `?framework=dag|disclosure|generic`
filters those lower tables only. Preserve `#lower` and `#upper` links.

There is exactly one upper track, for fully generic algorithms. Until generic admissibility is
proved and pinned, show the checked 106-cost adapter as a candidate, not an admitted record.
Do not relabel legacy DAG upper submissions as generic. The chart has one upper candidate line;
the upper leaderboard has no framework filter. Reject public submissions to legacy DAG upper roots.
Retain their proof files and historical pages as references, and preserve all existing demo rows.
The lower demo rows remain visible by default; legacy upper demos remain in historical solver pages.
Preserve Satoshi/Vitalik's existing demos. Generic lower includes Vitalik's demo at the checked
claim, with no invented improvement beyond it. The card, chart point, leaderboard, submission page
and solver profile must all refer to this same row.

Keep the rules concise and independent of current scores, candidate results and proof history.
Keep all key admissibility, cost, security and submission requirements available on the rules page;
use expandable details and diagrams to keep the overview readable. Explain partial disclosures
through their declared dependencies and the cut requirement, not blanket claims about named encodings.
A decoder is permitted as a declared downstream deterministic node; mathematical recoverability
alone does not replace a valid cut. Preserve the cut-reconstruction and shared-origin diagrams.
Partial-disclosure lower
uses `disclosure-lower` with the same baseline-relative demo offsets as DAG lower.
`seed_demo.py --refresh` preserves existing rows. Run isolated checks with
`.venv/bin/python -m unittest discover -s tests -v` from `service/` after changing this behavior.
