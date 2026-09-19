# Local leaderboard fixtures

`submissions.json` is the versioned source of the local demo leaderboard: fictional submissions by
Satoshi Nakamoto, Vitalik Buterin and Hal Finney on the five public tracks and the two legacy upper
references. A fresh clone needs no database dump. Run `uv sync --frozen` and `./run-local.sh` from
`service/`; startup creates the local database and loads these entries automatically.

Each entry has a permanent `id`, a `login`, an age `hours_ago` at first insertion, an `is_record`
flag, optional `assisted_by`, `co_authors` and `notes`, and an `improvement` over its track's
checked reference claim, in the track's unit. The displayed claim is the reference plus
`improvement` on lower tracks and the reference minus `improvement` on upper tracks: a positive
value beats the reference, a negative value falls short of it, and 0 matches it. Refreshing
recomputes claims from the current contract and inserts missing entries, preserving existing
database IDs and dates. Keep fixture IDs stable when editing a row. Every entry carries the visible
demo label.

On each public track, the rows form a record history whose latest record has `improvement: 0`, so
the current demo record matches the checked certificate; each non-record attempt falls short of
the record before it. The legacy upper rows improve on 106 and appear only in the historical
pages. RISC-V rows are seeded only while that track is admitted in the core metadata.

These are website fixtures, not proof submissions. Checked Lean certificates live in
`ots.golf-submissions`; fictional attribution and invented improvements do not establish a theorem.

`OTS_PHONY=0` skips automatic seeding. `seed_demo.py --refresh` reconciles the fixtures manually.
It accepts development mode and a loopback site URL only.
