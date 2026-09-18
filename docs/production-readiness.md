# Repository review — 17 September 2026

The checked certificates, service regressions, numerical checks and local browser audit pass.
The website and worker run the reviewed code on localhost. **Public deployment still requires
acceptance on the actual Linux host and a staging GitHub repository.** This review does not claim
that macOS testing establishes production isolation. Nothing was pushed or deployed. The original
operational review was committed locally as `1000826` on `main`; the later generic upper addition
is documented in [the generic proof report](generic-upper.md).

The review covered the formal contract and exports, verifier, queue/webhook/reporting service,
website, numerical tools, deployment configuration and documentation. Parallel reviewers owned
separate service, verifier and website files. That operational review did not change the protected
contract, certificates, claims, toolchain or pin. The subsequent generic upper addition changes
the challenge metadata and pin, with the underlying generic definitions preserved. The historical `Submissions/Upper` construction is untouched.

## Changes that matter

### Admission and operation

- Webhooks require the configured repository and a valid signature. Oversized or malformed payloads,
  malformed heads, renamed files outside the admitted root and truncated file lists are rejected.
  Admission rechecks the PR head and serializes quota decisions.
- Verification alone no longer promotes a PR. The verified head must also be confirmed merged by
  GitHub's API. A merge received before the result is retained and applied after verification.
- A durable GitHub reporting outbox retries statuses/comments independently of proof verification.
  Stored comment IDs allow updates. A crash between posting a new comment and saving its ID can
  still cause one duplicate on retry; this is documented, not an exactly-once guarantee.
- Process locks prevent concurrent workers and serialize shared database operations. A worker
  restart requeues interrupted work. Timeouts and termination clean up child processes and retain
  logs; malformed or inconsistent pipeline results cannot become verified records.
- Production web and worker processes have separate Unix identities. Only the web process receives
  GitHub credentials. Production settings validate the role, HTTPS origin, repository and secret;
  a credential-bearing worker refuses startup. Local startup also strips its GitHub credentials.
- Deployment now requires a dedicated bounded work filesystem. It leaves the services stopped
  until the acceptance checks pass. The guide covers backups, recovery, upgrades and monitoring.

### Verifier

- Submission exports enforce file types, names, counts and byte limits before copying. They reject
  symlinks, nested trees and special files, guard local file replacement/growth, and read Git blobs
  directly so `.gitattributes` cannot change the submitted bytes through archive attributes.
- Claims and imports receive stricter parsing. Git output is bounded and its subprocess groups
  are registered for cancellation. Existing `--work` directories cannot be overwritten.
- Linux verification refuses root, development shims and missing isolation. It requires Landlock
  ABI 3 or newer, systemd, a clean environment and enforced restrictions on networking, process
  control, `/proc`, `/sys`, devices and shared memory. The in-service launcher checks essential
  restrictions before starting comparator. Read-only system mounts also prevent metadata changes
  to trusted files; only the job’s `.lake` is writable. The actual-host probe tests filesystem, network,
  environment, process-memory and signal denial, including a live canary process.
- Each Linux job must live on a dedicated ext4/xfs or bounded tmpfs filesystem of at most 64 GiB,
  separate from persistent state, the trusted checkout/cache and the system. Nested mounts and
  loop-backed images are refused. Git staging uses that same bounded storage.
- The production memory/time limits remain 24 GiB and 20 minutes for comparator's process tree.
  macOS still uses comparator's development shim and is suitable only for trusted local checks.

### Website and maintenance

- The homepage states the question directly. The demo notice precedes the scores; fictional rows
  are identified on their submission and solver pages, without false verification badges or
  invented commit links. Existing Satoshi/Vitalik rows, dates and IDs are preserved.
- Light/dark contrast, keyboard navigation, narrow tables, chart targets, tooltip placement and
  reduced-motion behavior were checked and improved. Chart ticks stay bounded even for maximum
  allowed claims. Rules remain independent of scores, with the explanatory diagrams intact.
- Three lower frameworks and one generic upper track remain distinct. Legacy upper references
  are not relabeled. The subsequent generic upper certificate completes correctness, signing
  availability, security and cost; its challenge is pinned and the track is open.
- Inline scripts were moved into static files for the content security policy. Readable error
  pages and a database-aware health endpoint were added. Unused diagram code and obsolete CSS
  were removed. Demo tooling now refuses production mode and non-loopback origins.
- `tools/check_repo.py` provides one local regression command; `service/browser_check.py` provides
  a repeatable Firefox audit. Numerical search now charges node tweaks separately from the fixed
  message-and-nonce index, correctly reproducing the existing 106-cost forest.

## Original operational-review evidence

All checks used the existing trusted local Lean/tool caches. Unit tests use isolated databases
and temporary repositories. Browser checks read localhost and exercise its controls.

| Check | Result |
|---|---|
| Protected contract pin | Unchanged, passes |
| `lake build OptimalOTS Submissions` | Passes, 8,899 build jobs |
| `lake env lean scripts/check-axioms.lean` | Passes, expanded to 46 protected declarations |
| Verifier regression suite | 57 tests pass |
| Service regression suite | 56 tests pass |
| Numerical regression suite | 5 tests pass |
| Pinned comparator's upstream suite | 14 tests pass; macOS development shim |
| Static JavaScript and shell syntax | Passes |
| Locked Python environment | Dependency consistency and offline lock check pass |
| Paper | Builds, 9 pages |
| Firefox | Desktop and 320/390-pixel layouts, light/dark, keyboard, filters, tooltips, reduced motion and error pages pass |

The official verifier accepted every pinned certificate:

| Slug | Claim | Wall time |
|---|---:|---:|
| `generic-lower` | 1 | 151.6 s |
| `lower` | 18 | 191.9 s |
| `disclosure-lower` | 93 | 187.6 s |
| `upper` — historical reference | 106 | 250.1 s |
| `disclosure-upper` — historical reference | 106 | 247.3 s |

After the final verifier changes, the official Git-commit path also accepted `generic-lower` at
`1000826ac5bb2526dd3024d137c03a1a88f2bbf4`, claim 1, in 58.8 seconds. This exercises committed-byte
export and the final bounded subprocess helper; the log is
`/private/tmp/ots-review-commit-certificate.log`. All five policy checks pass as well.

After the commit hook refreshed localhost, its homepage displayed the new commit, all 26 reachable
internal HTML links returned successfully, and all 19 demo rows retained their IDs, claims and dates.
The web server and worker were both restarted with the reviewed implementation. Documentation links
in the updated READMEs and reports also resolve.

These are macOS proof-pipeline results, not Linux sandbox acceptance. The permitted exported axiom
set remains `propext`, `Quot.sound` and `Classical.choice`; no `sorry` or `native_decide` certificate
was admitted. The numerical tests reproduce whole-word 93 and show that 94 is not established by
that same attack arithmetic. They also reproduce the DAG and historical disclosure calculations.

Local logs are under `/private/tmp/ots-review-*`; the integrated build/audit/paper log is
`/private/tmp/ots-review-full-check.log`, final regression results are in
`/private/tmp/ots-review-final-regressions.log`, and final browser screenshots are in
`/private/tmp/ots-review-final-browser/`. These are local review artifacts, not committed assets.

To reproduce, prepare the service, numerical and Lean environments described in the READMEs, then:

```sh
python3 tools/check_repo.py --numerics-python .venv-tools/bin/python --formal --official --paper
python3 service/browser_check.py --output-dir /tmp/ots-ui
```

The runner requires Node.js for syntax checks; `--node /path/to/node` selects an existing binary.
The browser runner requires Firefox and a running seeded localhost preview.

## Generic upper admission update

Commit `8a4afb5` adds the complete generic upper certificate and opens the single public upper
track. Perfect correctness is proved for every DAG adapter. The concrete forest's signing failure
is at most `2^-256` for every public-key-dependent message choice, satisfying the pinned `2^-128`
allowance. Strong 127-bit security and the 106-compression verification bound are preserved exactly.
See [the mathematical argument and proof map](generic-upper.md).

The new contract pin is `b2b1ffdeb02aa410fe2133b6b7e652f6f55ddf357eb0c5cd58dbb877792303b2`,
covering 22 files. The protected generic definitions have only an introductory comment change;
the three lower statements, original Upper root, toolchain and library manifest are unchanged.
The independent GenericUpper root passes policy with 30 files and 446,047 bytes. All 20 inherited
construction/security modules are exact copies except for sibling import paths.

Current checks pass: 59 verifier tests, 59 service tests, 5 numerical tests, JavaScript and shell
syntax, the complete Lean build (8,927 jobs), and the 46-declaration protected-model axiom audit.
The official verifier accepted every configured certificate against this pin:

| Slug | Claim | Wall time |
|---|---:|---:|
| `generic-upper` | 106 | 157.3 s |
| `generic-lower` | 1 | 66.3 s |
| `lower` | 18 | 107.4 s |
| `disclosure-lower` | 93 | 103.6 s |
| `upper` | 106 | 152.9 s |
| `disclosure-upper` | 106 | 150.3 s |

Two deliberate negative submissions also compiled successfully and were then rejected by
comparator's statement matching: changing only the claim to 105 was rejected at `cost` (127.2 s),
and replacing the admissibility theorem's fixed `2^-128` allowance with a proved one-half allowance
was rejected at `admissible` (120.0 s). The latter leaves security and cost unchanged, confirming
that availability is enforced independently. The test copies were outside the repository.
Results are in `/private/tmp/ots-generic-admission-reject-claim-105.json` and
`/private/tmp/ots-generic-admission-reject-failure-half.json`.

Current Firefox checks pass on desktop and at 320/390-pixel widths, in light/dark mode, including
keyboard controls, sorting, tooltips, lower-only filters, four normal leaderboard tables, collapsed
rules, both diagrams, reduced motion and the HTML error page. The web process and worker were both
restarted after the implementation commit. The live footer shows that commit; 15 linked local
routes, including health, return successfully. All 19 prior demo rows retain their IDs, claims,
dates and attribution; only two separate generic upper demos were added, at 106 and 105. Fictional
rows remain labeled and are never presented as verified certificates.

Logs: `/private/tmp/ots-generic-admission-checks.log` and
`/private/tmp/ots-generic-admission-verify-<slug>.json`; browser screenshots:
`/private/tmp/ots-ui-generic-upper/`. These results do not replace the actual-host Linux isolation
or staging GitHub acceptance gates below. Nothing was pushed or deployed.

## Generality labels and rules presentation (2026-09-17)

The three lower classes are now displayed as Generality 3/3, 2/3 and 1/3. The Upper bound card
comes first and its chart line is solid. Rules explain the fixed budgets before the two tracks,
retain all admission requirements, and add a WOTS+ chain diagram. All nine sections start folded.

Only display metadata changed in the protected contract: framework titles and a historical title
for the original DAG upper reference. The new 22-file pin is
`491d82d7f56ef5885d2b1da0416063658f0b4cadb9f0c0353aec8a4a0ca6f644`.
Lean sources, challenges, claims and verifier requirements are unchanged; the official proof runs
above used the preceding pin and were not repeated for these presentation changes.

All 59 service tests and 59 verifier tests pass. Firefox checks pass on desktop and at 320/390
pixels, including the new labels, upper-card ordering, solid upper line, folded rules, three
diagrams, tooltips, filters and light/dark themes. Logs are in
`/private/tmp/ots-rules-generality-tests.log`, `/private/tmp/ots-generality-verifier-tests.log`
and `/private/tmp/ots-ui-generality.log`; screenshots are in `/private/tmp/ots-ui-generality/`.

## Shared algorithm availability and concise presentation (2026-09-17)

Both algorithm challenges now fix signing failure at most `2^-128`. The generic lower export
specializes the retained lemma for every allowance at most one half; the certified claim remains 1.
The protected interface's mathematical definitions, both DAG lower statements and all upper proof
files are unchanged. The new 22-file pin is
`fd04517f1f73521d46ca98afb9c7e43d34df60f7d9fded3a1fdcb9817c3023fb`.

The official verifier accepted `generic-lower` at 1 in 53.0 seconds and `generic-upper` at 106
in 152.0 seconds. A temporary lower submission narrowed to failure at most `2^-256` compiled,
then comparator rejected its statement in 58.8 seconds. This checks enforcement of the exact
class quantified over. Results: `/private/tmp/ots-unified-availability-{lower,upper,reject-narrow}.json`.

The full Lean build passed (8,927 jobs), as did the 46-declaration protected-model axiom audit,
60 verifier tests and 59 service tests. Logs: `/private/tmp/ots-availability-{full-build,axioms}.log`
and `/private/tmp/ots-concise-{verifier,service}-tests.log`.

The website and current proof guides now define objects through their structure and allowed
operations. Public prose calls injective encoding “lossless encoding.” The two framework
diagrams were removed; the WOTS+ list of message and checksum chains remains. All nine rule
sections start folded, with the bound direction explicit in framework headings. The Justin Drake
explanation remains alongside the actual-input cost rule.

Homepage lower cards explicitly say “Lower bound” and show compression units. At 1360 pixels,
the upper card is 24.0% shorter and each lower card is 25.3% shorter. Firefox checks passed
on desktop and at 320/390 pixels, with light/dark themes, controls, filters, tooltips and
horizontal scrolling. Screenshots and logs: `/private/tmp/ots-ui-concise/` and
`/private/tmp/ots-ui-concise.log`. Card measurements: `/private/tmp/ots-cards-{before,after}.json`.

## Separate core and proof repositories (2026-09-18)

The core is `leanEthereum/ots.golf-dev`; proof PRs, result reporting and record promotion use
`leanEthereum/ots.golf-submissions`. `OTS_REPO_ROOT` still selects the trusted core checkout.
`OTS_SUBMISSIONS_REPO` is a separate, explicit admission setting. Rules, source links, setup
instructions and PR templates distinguish the repositories. The protected contract is unchanged.

Each PR's base repository is retained in its stored URL. Tests cover core-repository webhook
rejection, a forked submission checked by the core verifier, identical PR numbers and heads in
different repositories, and old outbox jobs remaining separate without blocking new reports.
The workspace preparation tool creates only the four public roots and a pinned core submodule,
refuses dirty sources or existing destinations, and performs no network or publishing operations.

Local validation: `tools/check_repo.py` passes 68 service tests, 60 verifier tests and 7 tooling
tests, plus JavaScript and shell syntax checks. The Firefox audit passes desktop and 320/390-pixel
layouts, rules, filters, keyboard controls and demo presentation. Both localhost processes were
restarted with the new settings. All 21 demo rows retain their IDs, dates and scores.
Evidence: `/private/tmp/ots-repo-split-checks.log`, `/private/tmp/ots-repo-split-browser.log`
and `/private/tmp/ots-repo-split-browser/`.

All four exported roots pass policy checks; their 83 files match the core references byte for byte.
The official verifier accepts submissions commit `da16887`, using core commit `402365c`:
`generic-lower` at 1 in 81.8 seconds and `generic-upper` at 106 in 173.3 seconds. These macOS
checks validate the proofs, not production isolation. Results:
`/private/tmp/ots-repo-split-official-{lower,upper}.json`.

The empty GitHub submissions repository was cloned locally, then populated with that same
verified commit and pinned core submodule. The new commits remain local; no remote branches
were changed.

These checks use mocked GitHub APIs; webhook installation, token permissions and real GitHub
acceptance remain launch tasks. This change does not deploy or publish either repository.

## Gates before public launch

Follow [the deployment guide](../service/deploy/README.md) on the intended host. Do not infer any
of the following from a successful local proof check:

1. Run the Linux isolation probe and every configured official certificate under the deployed identities.
   Exercise memory exhaustion, timeout and a full work volume. Confirm complete process cleanup,
   preserved website/database availability and refusal when isolation is unavailable.
2. Confirm web credentials are unreadable to the verifier identity, effective systemd restrictions,
   HTTPS/proxy configuration, private backups and a successful database restore.
3. In a staging GitHub repository, test signed and duplicate webhooks, rejection, verification,
   merge-before-verification, API outage/recovery and worker restart. Only an API-confirmed merged
   head may become a record. The local tests mock GitHub and cannot replace this check.
4. Before upgrading an existing deployment, audit historical real rows marked `is_record` against
   their merged PRs: the previous implementation promoted at verification time. An automatic
   rewrite would risk discarding legitimate history, so this review makes no such migration.

The host bootstrap downloads system tooling and is not a reproducible operating-system image.
No online dependency-vulnerability scan, public load test, live GitHub mutation or Linux runtime
acceptance was performed. This is a single-host deployment; the process locks are not a distributed
queue protocol. Review those constraints before changing the deployment topology.

## RISC-V upper bound track certified and admitted (2026-09-18)

`formal/Submissions/RiscvUpper/` now holds a complete `Riscv.Submission.Certificate` at
**229113 virtual cycles**: the fixed-layout forest OTS, its 114557-instruction RV64IM verifier
image, a proof that the image's complete oracle computation equals the certified Lean verifier on
every public key, message and raw signature bit string (so every execution terminates, including
rejections, with the specified queries in the specified order), and the accepting-execution cycle
bound. `Solution.lean` exports `OptimalOTS.Challenge.RiscvUpper.{submission,certificate}` with
`claim.txt` 229113. The certificate uses only `propext`, `Classical.choice` and `Quot.sound`.
The proof map is in [the track notes](riscv-upper.md).

The metadata now admits two upper tracks through top-level `upper_tracks`
(`generic-upper`, `riscv-upper`); the three frameworks classify lower bounds only, and
`frameworks.generic.upper_track` was removed. The new track has `cost_unit` "virtual cycles",
baseline 229113, the RISC-V challenge stub and comparator configuration as protected files, and
imports limited to `Mathlib`, `VCVio`, `OptimalOTS.{Statement,Algorithm,RiscvMachine,Riscv}`
plus siblings. The new 26-file pin is
`c5d61d622981c63015fc2215817cdaf16efcc4b1be620dd4aee827cc0f690c41`. The protected Lean
interfaces and every other track's statement, claim and root are unchanged.

The official verifier accepted `riscv-upper` at 229113 against this pin in 547.2
seconds on macOS; the run compiles the whole root, including the kernel-checked image validity
and cycle-cap decisions, well inside the 20-minute limit. Result:
`/private/tmp/ots-riscv-official-verify.json`. The policy check reports 69 files and 816,043 bytes in the root.

The website shows the checked claim as a separate "RISC-V upper bound" card, leaderboard and
chart with an independent cycle axis; compression bounds are never combined with cycles. Rules
gained a folded RISC-V section stating the machine, refinement, termination and accepting-cycle
requirements, without scores. One Satoshi-attributed demo fixture at zero improvement seeds only
when the track is admitted; all 21 earlier demo rows keep their IDs, dates, claims and attribution.

Checks: the complete Lean build (9008 jobs), the 65-declaration protected-model axiom audit and
the RISC-V machine boundary checks pass (`/private/tmp/ots-riscv-{full-build,check-axioms,check-machine}.log`);
61 verifier tests and 75 service tests pass (`/private/tmp/ots-riscv-activation-tests.log`);
the Firefox audit passes on desktop and phone widths, both themes, the two upper charts and
their tooltips, five leaderboard tables, folded rules and the eye animation
(`/private/tmp/ots-final-browser.log`, screenshots in `/private/tmp/ots-final-browser/`).
These macOS runs validate the proofs and presentation, not production isolation. Nothing was
pushed or deployed; the submissions checkout is pinned to the local core commit.
