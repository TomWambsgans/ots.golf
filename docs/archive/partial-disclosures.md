# Historical partial disclosures from 46 hash outputs

This document records the former third framework and its verification at commit `84c5fd2`.
The active third lower framework is now [whole words](../whole-words.md). Its retained
`disclosure-lower` slug and root export a different, explicitly pinned contract. The historical
`disclosure-upper` certificate remains locally verifiable and is not a whole-word construction.
The scores, commands and website descriptions below describe that earlier milestone.

The third framework retains the existing bare-oracle DAG contract and adds one condition:
apart from the nonce, the disclosed payload has at most 46 distinct hash origins. Sources
contribute no hash origin, a hash output contributes its own node, and a deterministic operation
inherits the union of its parents' origins. Multiple fragments of one output count once.

This permits arbitrary bit widths, DAG sharing, deterministic combinations and partial
Reed–Solomon encodings. A codeword derived from one hash digest has one origin; one derived
from several digests has all of their origins. Actual disclosed bits still count toward the
5248-bit payload limit. The 127-bit security requirement and all oracle costs are unchanged.
Verification still uses the existing graph cut and forward reconstruction rules. Arbitrary
decoding from an insufficient structural cut is not admitted by this change.

## Paper argument

For a reconstruction pattern R, collapse deterministic paths between hashes. Its boundary B
consists of the immediate hash dependencies of R which are outside R. Every boundary hash is
an origin of a disclosed value, so |B| <= 46. Secret sources need no binary decision.

If every verification costs at most 79, the index and root leave at most 77 nonroot hashes.
An ordered traversal recording recompute/stop decisions gives a prefix-free encoding with at
most 77 zeros and 46 ones. Padding yields at most binomial(123,46) patterns. Equivalently,
split the family on its highest remaining hash: including it spends one recomputation;
excluding it spends one boundary element. Pascal's recurrence gives the same bound.

For M=2^115 indices partitioned into K classes of sizes k_j, T=2^122 nonce trials give average
success at least sum_j k_j^2/(64+k_j)/M >= M/(64K+M), by Cauchy–Schwarz. Multiplying by the
fresh-message factors (9/10)^2 and signing success 256/257 gives success > 33/1000 when
K <= binomial(123,46). The full attack costs at most 1024+2^20+2^122+2*78+2, whose ratio to
2^127 is < 4/125. This contradicts security and establishes the bound 80.

## Implementation status

The predicate is defined in `formal/OptimalOTS/Disclosure.lean`. Both new certificates build:

```lean
OptimalOTS.Challenge.DisclosureLower.candidate :
  DisclosureVerificationLowerBound paperParams 46 80

OptimalOTS.Challenge.DisclosureUpper.scheme : Scheme paperParams
OptimalOTS.Challenge.DisclosureUpper.secure : scheme.Secure
OptimalOTS.Challenge.DisclosureUpper.cost : ∀ i, scheme.verifyCost i ≤ 106
OptimalOTS.Challenge.DisclosureUpper.disclosure : scheme.DisclosureBound 46
```

The lower proof uses ordered set families rather than implementing the traversal itself.
`DisclosureLower/OrderedCounting.lean` proves the abstract binomial bound;
`DisclosurePatterns.lean` supplies the origin witness. The `Averaged*` modules establish the
exact signing law, reciprocal search bound, Cauchy–Schwarz average and experiment assembly.
The upper certificate copies the existing forest's security proof into its own flat root and
proves the stronger origin bound 41. Neither original submission root was edited.

The candidate axiom guard accepts only `propext`, `Classical.choice`, and `Quot.sound`.
`lake build OptimalOTS Submissions` passes (8890 jobs), including the existing generic adapter.
All four submission-policy checks pass. The official comparator accepted both new tracks and
both original tracks:

| Track | Claim | Result | Time |
|---|---:|---|---:|
| disclosure-lower | 80 | verified | 113.3 s |
| disclosure-upper | 106 | verified | 172.3 s |
| lower | 18 | verified | 96.8 s |
| upper | 106 | verified | 153.4 s |

Commands: `python3 verifier/verify.py <track> --source . --keep`.
Contract pin: `269b181fdbfbb44b529e664ab403b7268cfb5e3ef07c79ef4b51e27d8ca18266`.
Local logs:

- Disclosure lower: (local log).
- Disclosure upper: (local log).
- Original lower: (local log).
- Original upper: (local log).

`tools/tune_lower_bound.py --method disclosure --claims 80,81` independently confirms the exact
arithmetic at 80; the same estimate fails at 81. This numerical tool is not a certificate.
The full proof, rather than the search, establishes 80. No optimality claim for that bound is made.

The unrestricted DAG certificates remain 18 and 106; the upper certificate is now a reference proof.
Generic lower submissions are open with a certified baseline of 1; generic upper admission still
awaits the adapter's correctness and signing-availability proofs. The site's
combined chart and framework-specific rankings keep these scopes separate; the local demo board retains its invented
Satoshi/Vitalik submissions with claims relative to each framework's baselines.

The formal milestone is local commit `84c5fd2` on `main`. Eleven service regression tests pass
with `cd service && .venv/bin/python -m unittest discover -s tests -v`, covering independent
record attribution, the combined chart, lower leaderboard filters, generic admission status, the single
generic upper candidate, demo refresh preservation, solver and submission links, public rejection
of legacy upper submissions, and pull-request root matching. Later rules tests ensure the rules
remain independent of scores.
Localhost serves the combined view and all three lower filters successfully; demo lower records
are 20 for DAGs and 82 for partial disclosures. The old 101-cost upper demo rows remain in historical
pages only. These invented claims are separate from the kernel-verified baselines. The commit hook
refreshes localhost and adapts demo claims automatically.

The website has three lower-bound frameworks and one fully generic upper track. The chart shows
three lower series, now including the separate [checked generic lower bound of 1](../generic-lower.md)
for correct schemes whose signing succeeds at least half the time, plus a single
106-cost generic adapter candidate. The candidate is not an admitted upper record: correctness and
signing availability remain to be proved. Lower framework filters do not split the upper track.
Legacy DAG upper certificates remain locally verifiable and their historical pages remain accessible;
the public queue rejects new submissions to those legacy upper roots. No existing demo rows are removed.

Browser checks in headless Firefox passed for direction switches, per-table sorting, keyboard chart
tooltips, filtered deep links, rule expansion, and a narrow layout with horizontally scrollable charts
and tables. This website update changes no Lean statements, submission roots, verifier settings or
contract pins.
