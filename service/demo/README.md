# Local leaderboard fixtures

`submissions.json` is the versioned source of the Satoshi Nakamoto and Vitalik Buterin demo
leaderboard. A fresh clone needs no database dump. Run `uv sync --frozen` and `./run-local.sh`
from `service/`; startup creates the local database and loads these entries automatically.

Each entry has a permanent `id`, an author, an age in hours at first insertion, and an
`improvement` relative to its track's checked reference claim. Refreshing adjusts scores to the
current contract and inserts missing entries, while preserving existing database IDs and dates.
Keep fixture IDs stable when editing a row. All entries retain the visible demo label.

These are website fixtures, not proof submissions. Checked Lean certificates live in
`ots.golf-submissions`; fictional attribution and invented improvements do not establish a
theorem. A demo score can match a checked certificate by using `improvement: 0`.

Hal Finney's rows never change an earlier record: his Generality 2/3 record follows Satoshi's,
his other rows match without beating the record before them, and his legacy records sit between
existing ones. The RISC-V Satoshi fixture has zero improvement and appears only when that track is admitted
in the core metadata. Its score uses virtual cycles; the existing entries keep their original units.

`OTS_DEMO_DATA=0` skips automatic seeding. `seed_demo.py --refresh` reconciles the fixtures
manually. It accepts development mode and a loopback site URL only.
