# Repository review — 17 September 2026

The checked certificates, service regressions, numerical checks and local browser audit pass.
The website and worker run the reviewed code on localhost. **Public deployment still requires
acceptance on the actual Linux host and a staging GitHub repository.** This review does not claim
that macOS testing establishes production isolation. Nothing was pushed or deployed.

The review covered the formal contract and exports, verifier, queue/webhook/reporting service,
website, numerical tools, deployment configuration and documentation. Parallel reviewers owned
separate service, verifier and website files. No protected contract, certificate, claim, toolchain
or contract pin changed. The historical `Submissions/Upper` construction is untouched.

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
- Three lower frameworks and one generic upper candidate remain distinct. Legacy upper references
  are not relabeled. Generic upper admission still needs correctness and signing-availability
  proofs and its pinned challenge; this review does not establish them.
- Inline scripts were moved into static files for the content security policy. Readable error
  pages and a database-aware health endpoint were added. Unused diagram code and obsolete CSS
  were removed. Demo tooling now refuses production mode and non-loopback origins.
- `tools/check_repo.py` provides one local regression command; `service/browser_check.py` provides
  a repeatable Firefox audit. Numerical search now charges node tweaks separately from the fixed
  message-and-nonce index, correctly reproducing the existing 106-cost forest.

## Validation evidence

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

## Gates before public launch

Follow [the deployment guide](../service/deploy/README.md) on the intended host. Do not infer any
of the following from a successful local proof check:

1. Run the Linux isolation probe and all five official certificates under the deployed identities.
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
