# Local leaderboard fixtures

`submissions.json` is the versioned source of the local demo leaderboard: fictional submissions by
Satoshi Nakamoto, Vitalik Buterin and Hal Finney on the five public tracks and the two legacy upper
references. A fresh clone needs no database dump. Run `uv sync --frozen` and `./run-local.sh` from
`service/`; startup creates the local database and loads these entries automatically.

Each entry has a permanent `id`, a `login`, an age `hours_ago` at first insertion, an absolute
`claim` in the track's unit, an `is_record` flag, and optional `assisted_by`, `co_authors` and
`notes`. Refreshing resets existing demo rows to their fixture claims and inserts missing entries,
preserving database IDs and dates. Keep fixture IDs stable when editing a row. Every entry carries
the visible demo label.

On each public track, the rows form a record history whose best record equals a claim proven in
the reference proofs; older records and non-record attempts may be worse. When a reference proof
changes, update that track's best claim here. The legacy upper rows appear only in the historical
pages. RISC-V rows are seeded only while that track is admitted in the core metadata.

These are website fixtures, not proof submissions. Fictional attribution does not establish a
theorem; record decisions for real submissions ignore demo rows.

`OTS_PHONY=0` skips automatic seeding. `seed_demo.py --refresh` reconciles the fixtures manually.
It accepts development mode and a loopback site URL only.
