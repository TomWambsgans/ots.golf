# Partial disclosures from 46 hash outputs

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
K <= binomial(123,46). The full attack costs at most 1024+2^21+2^122+2*78+2, whose ratio to
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

- Disclosure lower: `/private/var/folders/7g/qxrr2pgj40s3ykbngr10jkkr0000gn/T/ots-verify-g2xf0era/verify.log`.
- Disclosure upper: `/private/var/folders/7g/qxrr2pgj40s3ykbngr10jkkr0000gn/T/ots-verify-hqlgjeg8/verify.log`.
- Original lower: `/private/var/folders/7g/qxrr2pgj40s3ykbngr10jkkr0000gn/T/ots-verify-ed7pb0__/verify.log`.
- Original upper: `/private/var/folders/7g/qxrr2pgj40s3ykbngr10jkkr0000gn/T/ots-verify-3tb6vucu/verify.log`.

`tools/tune_lower_bound.py --method disclosure --claims 80,81` independently confirms the exact
arithmetic at 80; the same estimate fails at 81. This numerical tool is not a certificate.
The full proof, rather than the search, establishes 80. No optimality claim for that bound is made.

The unrestricted DAG records remain 18 and 106. The generic algorithm framework remains at its
documented foundation stage until correctness and signing availability are certified. The site's
three framework views keep these scopes separate; the local demo board retains its invented
Satoshi/Vitalik submissions with claims relative to each framework's baselines.

The formal milestone is local commit `84c5fd2` on `main`. Six service regression tests pass
with `cd service && .venv/bin/python -m unittest discover -s tests -v`, covering independent
records and charts, the generic foundation page, demo refresh preservation, submission links,
rules and pull-request root matching. Localhost serves all three framework views successfully;
the demo boards show 20–101 for DAGs and 82–101 for partial disclosures. These invented
demo claims are separate from the kernel-verified baselines reported above. The commit hook
refreshes localhost and adapts demo claims automatically.
