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

`./run-local.sh` refreshes the demo board without replacing rows before starting the worker and web server; use this entry
point for local development. `OTS_DEMO_DATA=0` explicitly disables startup seeding.
`seed_demo.py` refuses production mode and non-loopback site URLs even with `--force`, and
refuses nonlocal databases by default. Never force it against production.

If reseeding an already running site, wait for any active baseline verification to finish before
running `.venv/bin/python seed_demo.py`: the seed replaces baseline database rows.
For ordinary updates, `bash refresh-local.sh` preserves submission IDs and dates and leaves
real submissions alone, so it is safe while the worker is running.

The three frameworks apply only to lower bounds. All three lower tracks are open, and the homepage
plots three certified lower series from their normal `challenges.json` metadata. Generic lower uses
`generic-lower`, with baseline 1 and signing failure at most `2^-128` for every public-key-dependent
message selection, matching the upper track. Do not hardcode a separate generic
foundation certificate or show lower admission as pending. If a future framework has no checked
certificate, use a pending lane outside the numeric axis. Never substitute zero or a DAG theorem
for a missing generic certificate. Lower leaderboards have separate
rankings for generic algorithms, DAGs and whole words; `?framework=dag|disclosure|generic`
filters those lower tables only. Preserve `#lower` and `#upper` links.

Upper tracks are admitted through the top-level `upper_tracks` metadata, independently of the
three lower frameworks. `generic-upper` is “Upper bound”, measured in compressions. `riscv-upper`
is “RISC-V upper bound”, measured in virtual cycles on accepting executions; every execution
must still terminate and refine the Lean oracle specification. Render the second card, chart,
leaderboard and rules section only after its checked certificate is pinned and admitted. Its chart
has an independent cycle axis: never combine virtual cycles with compression bounds. The
compression upper line remains solid. Both upper leaderboards stay outside the lower-framework
filter. Reject public submissions to legacy DAG upper roots; retain their historical pages.
Preserve all existing demo entries. The additional Satoshi RISC-V fixture has zero improvement
relative to the checked claim, retains its demo label, and seeds only after admission.
The `disclosure-upper` reference belongs to Historical partial disclosures, not Whole words.
Use its `historical_framework_title` metadata on submission and solver pages. Its 16-bit tweaks
violate the whole-word restrictions; never present it as a whole-word upper construction.
The lower demo rows remain visible by default; legacy upper demos remain in historical solver pages.
Preserve Satoshi/Vitalik's existing demos. Generic lower includes Vitalik's demo at the checked
claim, with no invented improvement beyond it. The card, chart point, leaderboard, submission page
and solver profile must all refer to this same row.
Generic upper adds its own Vitalik demo at the checked claim and a later Satoshi demo one compression
lower. Preserve the previous 19 rows, their IDs and dates. These new scores are also fictional,
clearly marked as demos; they never receive verified badges or fabricated commit links.

Keep the rules concise and independent of current scores, candidate results and proof history.
Keep all key admissibility, cost, security and submission requirements available on the rules page;
use titled sections that are all collapsed on a fresh visit, beginning with “What is a one-time
signature?”. Teach the concepts before the exact requirements, and keep diagrams inside the
relevant sections. Combine overlapping topics and keep introductory explanations brief, linking
to reliable background reading (such as Wikipedia for Lamport and the RFC for WOTS+) instead of
repeating tutorials. Keep competition-specific requirements on the page. Preserve direct links
that open the requested section. Whole words uses independent
128-bit sources, 256-bit hash outputs with two selectable halves, and concatenation of whole-word
sequences. Concatenations can reorder, repeat or be empty; no other deterministic operations,
smaller fragments or encodings are admitted. Literal constant words cannot be introduced by a
deterministic node; hashing an empty input is allowed and charged. Hash inputs have no fixed arity;
charge their complete length. A 5,248-bit payload fits at most 41 words, plus the 256-bit nonce.
The framework definitions use prose; keep the removed DAG and whole-word diagrams out of the rules.
Whole-word lower keeps the compatibility slug/root `disclosure-lower`/`DisclosureLower`, with
the same baseline-relative demo offsets as DAG lower. Do not leave the old 46-origin rule on the site.
`seed_demo.py --refresh` preserves existing rows. Run isolated checks with
`.venv/bin/python -m unittest discover -s tests -v` from `service/` after changing this behavior.

After editing worker code, restart the local worker as well as refreshing the web process;
`uvicorn --reload` does not reload the worker. Keep one worker per data directory. Production web
and worker run as different Unix users; only the web process receives GitHub credentials.
Records require verification plus an API-confirmed merge of that exact head. Preserve reporting
retries and merge-before-verification handling. Never bypass Linux isolation or bounded-storage
checks to make a host pass. See `deploy/README.md` for the launch gates.

Use `browser_check.py` for repeatable Firefox checks of the seeded local preview. Keep demo labels
on individual entries and submission/profile pages; fictional rows must not present kernel
verification badges or fabricated commit links. A passing macOS proof check does not establish
production sandbox safety.

Keep the homepage headline “Think one-time signatures are easy? Prove it.” The mandala forms
the iris of an eye, with a dark pupil and a small catchlight. The eye fills its illustration
column. Choose a fresh random interval of four to eight seconds between blinks, and change the
signature highlights only while the eye is fully closed. Pause automatic motion when the page
is hidden or reduced motion is requested.
Keep the homepage concise: each upper card shows
its linked title, attributed record and cost; detailed requirements belong in the rules.
Do not restore the removed paragraph beginning “Each lower-bound class has its own optimum.”
Keep the heading “One upper bound. Three lower bounds.” removed from the homepage.
Keep the “Local demo leaderboard” explanatory banner removed; retain individual demo tags.

Use “Upper bound” as the public track name throughout the site, not “Generic upper”. Keep the
existing `generic-upper` identifier for URLs, data and verification. Show its score card before
the three lower cards and draw its chart line solid. Explain in the rules that any oracle algorithm
is allowed. Introduce the competition through fixed size, security and key-generation/signing
budgets, with worst-case verification cost as the quantity to minimize. Present the upper tracks and lower direction,
then the three lower classes; do not invent percentages for their degree of generality. Keep the
WOTS+ illustration as a list of chains, showing a selected signature value on each message and
checksum chain, with the remaining verification steps and per-step key/mask explanation. Do not restore
the removed background-reading disclaimer or historical-certificate paragraph in the rules.
Keep the compression-cost rationale crediting Justin Drake: a per-key public parameter can be
absorbed once as a full prefix block and its hash state reused. This motivates no implicit
per-query surcharge; it does not exempt bits explicitly present in an oracle input from cost.

Name the lower frameworks “Generality 3/3” (any oracle algorithm), “Generality 2/3” (a DAG with
arbitrary deterministic functions), and “Generality 1/3” (a DAG built from whole words). Use these
names in cards, charts, filters, leaderboards, rules and submission/profile pages; explain the
restrictions in the descriptions. Keep the existing slugs and Lean names. Historical upper
references retain their historical names; the generality levels apply only to lower bounds.

Keep the homepage score cards compact, with the correct cost unit beside every score.
Use “lossless encoding” in public prose for the contract's injective signature encoding.
Name the bound direction explicitly in each score-card and framework rule heading. The algorithm
rule section covers upper constructions and Generality 3/3 lower bounds; the RISC-V section states
its machine, refinement, termination and accepting-cycle requirements.
