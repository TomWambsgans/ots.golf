# ots.golf — plan

## Goal
A two-track, Lean-kernel-verified competition on the worst-case verification cost of graph-based
hash-based one-time signatures (128-bit public key, signatures ≤ 5504 bits, 127-bit security).
Current interval: **25 ≤ optimum ≤ 106** hash units.

- **Upper track** (minimize): a concrete `Scheme paperParams`, a proof that it is `Secure`, and a
  proof that every index verifies in ≤ c. A record needs c ≤ record − 1.
- **Lower track** (maximize): a proof of `VerificationLowerBound paperParams c`. A record needs
  c ≥ record + 1.

## Fixed decisions
| Topic | Decision |
|---|---|
| Contract | `formal/OptimalOTS/Statement.lean`, audited, then hash-pinned as `ots-v1`. Any change → v2, both tracks re-baseline. |
| Model | The paper's DAG model only (sources, deterministic nodes, hash nodes, disclosure sets), enforced by the type `Scheme paperParams`. |
| Upper certificate | `def scheme : Scheme paperParams`, `theorem secure : scheme.Secure`, `theorem cost : ∀ i, scheme.verifyCost i ≤ <literal>`. |
| Lower certificate | `theorem candidate : VerificationLowerBound paperParams <literal>`. |
| Claimed score | Read from `claim.txt`, rendered as a literal into the challenge stub before verification. |
| Submission | A git commit (pull request or API). Flat root per track, only `.lean` + `claim.txt`. Imports: Statement, sibling files, Mathlib, VCVio. Protected files untouchable. |
| Axioms | `propext`, `Quot.sound`, `Classical.choice` only (excludes `native_decide`). |
| Verifier | Own server. `leanprover/comparator` + landrun + systemd-run. 20 min wall clock, 24 GiB, no network, cached Mathlib/VCVio. |
| Ranking | Strict integer improvements are records. Other verified submissions listed by date. |
| Attribution | GitHub handle. Optional co-authors, model used, markdown description. |
| Profile / prizes | One profile (`paperParams`). No prizes. Apache 2.0. |

## Workstream A — Lean contract (repo)
1. Restructure: protected files (toolchain, lakefile, manifest, `formal/OptimalOTS/Statement.lean`, challenge
   templates, comparator configs, `challenges.json`) + `formal/Submissions/Lower/` + `formal/Submissions/Upper/`.
2. Move today's proof into `formal/Submissions/Lower/` (renamed namespace), `claim.txt = 25`.
3. Write the two challenge templates, `render-challenge.py` (claim → literal) and
   `check-submission.py` (flat root, import whitelist, size caps, protected hashes).
4. Write `check-axioms.lean` for the protected path.
5. Audit `Statement.lean` against the paper: `CostAtMost` / `IsQueryBound`, the `Secure` bound and
   budget range, index computation, signature length check, trial limit, label injectivity,
   reveal and keygen budgets. Fix, then pin the hash.
6. When the 106-unit proof is ready: add it as `formal/Submissions/Upper/`, `claim.txt = 106`.
7. `AGENTS.md` and `llms.txt`.

## Workstream B — Verifier service (server)
- Box: Ubuntu 24.04, ≥ 8 cores, 64 GB RAM, NVMe. Stack: Postgres, FastAPI, one worker, Caddy.
- Day 1: build toolchain, comparator, lean4export, landrun; warm Mathlib/VCVio;
  **time the baseline build** (validates the 20-minute limit).
- Pipeline, one job at a time: fetch commit → protected-hash and root checks → render claim →
  comparator in sandbox → store verdict/score/log → GitHub status + PR comment →
  record, or "verified, not a record".
- Entry points: GitHub App webhook (pull requests) and bearer-token API (after GitHub login).
  Same queue.
- API: public reads (tracks, leaderboard, state, submission); authenticated: submit, list own,
  update description, read log. Limits: 1–2 in flight per user, queue cap, 429 when busy.
- Ops: unprivileged worker, secrets only in the API process, nightly DB dump, rebuildable from a
  setup script.

## Workstream C — Site (ots.golf)
- Home: interval bar (progress = 1 − gap / 81), two record leaderboards, verified-non-record lists.
- Submission pages: status, score, attribution, description, source download, diff vs base.
  Solver pages.
- Rules page: the model in words, contract version and hash, limits. Literature points with
  caveats (paper's constant-sum Winternitz at 108; other Winternitz variants computed in this
  cost model; Lamport does not fit the signature budget).
- `/llms.txt`, OpenAPI docs, GitHub login.

## Milestones
1. **M1** — lower baseline (25) verifies end to end on the server through comparator.
2. **M2** — a test pull request on the lower track gets a verdict and a comment; the site shows it.
3. **M3 (gate)** — upper baseline (106) verifies; audit done; hash pinned as `ots-v1`. **Launch.**
4. **Post-launch** — second kernel (nanoda) as an independent check; second parameter profile if
   there is demand.

## Risks
- Baseline compile time vs the 20-minute limit: standalone lower submissions recompile the whole
  proof. Fallback: raise the limit for that track.
- The upper baseline proof is the critical path and the non-vacuity guarantee for the lower track.
- A statement bug found after launch forces contract v2.

## Open defaults
GitHub org named after the site; Hetzner; Python/FastAPI + Postgres.
