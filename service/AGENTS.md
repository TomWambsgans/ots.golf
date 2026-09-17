# Local preview

The user wants the invented Satoshi Nakamoto and Vitalik Buterin submissions present on localhost
by default. Preserve or restore those demo rows when updating the running local site. Do not
replace the demo board with a baseline-only board unless the user explicitly requests it.

`./run-local.sh` seeds the demo board before starting the worker and web server; use this entry
point for local development. `OTS_DEMO_DATA=0` explicitly disables startup seeding.
`seed_demo.py` refuses nonlocal databases by default. Never force it against production.

If reseeding an already running site, wait for any active baseline verification to finish before
running `.venv/bin/python seed_demo.py`: the seed replaces baseline database rows.
