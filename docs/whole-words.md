# Whole-word lower framework

The third lower framework is now `WholeWordVerificationLowerBound paperParams c`, defined in
`formal/OptimalOTS/WholeWords.lean`. It replaces the partial-disclosure class; the historical
`disclosure-lower` URL, submission root and export namespace are retained. The generic and
unrestricted DAG contracts are unchanged. There is still one upper track, for generic algorithms.

## Exact restriction

Secret sources are independent uniform 128-bit words. Hashing returns 256 bits; either fixed
128-bit half can be used. The only other deterministic operation is concatenation. Any number
of earlier words may be concatenated, with repetition and reordering allowed. Nested groups of
whole words, complete hash outputs and empty concatenations are also permitted. There are no
nonempty constant nodes, arbitrary functions, encodings or partial-word disclosures. Selecting
a half means a fixed choice declared in the graph, not a choice dependent on a value.

Every node carries a sequence of whole words; a signature discloses complete node values. All
original DAG cut, root reconstruction, nonce/index, size and resource requirements remain:
5248 payload bits plus a 256-bit nonce, 128-bit public key, 1024 key-generation compressions,
2^21 signing trials, 2^115 accepted indices out of 2^128, and 127-bit weak unforgeability.
Hash inputs have no fixed arity. One shared random oracle answers equal inputs equally; each
hash call costs at least one compression and one per started 512-bit input block.

This restriction rules out arbitrary Reed–Solomon encoding and partial bits. Such operations
remain available in the unrestricted DAG and generic frameworks. No origin limit is imposed
on entrants: the bound below follows from the permitted syntax and existing payload size.

## Proof on paper

An origin is the first hash reached while tracing a value backwards through deterministic nodes.
A secret source has no origins. A 256-bit hash has one origin; either 128-bit half has that same
origin. Concatenation unions origins and adds bit lengths. By induction along the graph,
128 times a value's number of distinct origins is at most its length. Taking the union across
all disclosed values preserves this inequality. The 5248-bit payload therefore has at most
41 origins, including when values are repeated or both halves of the same hash are disclosed.

Suppose all verifications cost at most 92. The index costs one, leaving at most 91 reconstruction
compressions and 90 nonroot hash nodes in a reconstruction pattern. For two different patterns,
the greatest hash in their difference is an origin of the other payload. Splitting the family
at its greatest hash and applying Pascal's recurrence bounds the number of patterns by
K = choose(90+41,41) = 17045107199267405351949642923536400.

Group M=2^115 indices by equal reconstruction pattern. A signature for one index can be
converted into a signature for another index in its class. With T=2^122 nonce trials, a class
of size k has search success at least k/(64+k). The exact signing law and Cauchy–Schwarz give
weighted success at least (256/257) M/(64K+M). Both randomly chosen messages are fresh with
probability at least 99/100; the second also differs from the signed message. Thus success is
at least (99/100)^2 (256/257) M/(64K+M), approximately 0.035811061437.

The entire experiment costs at most B=1024+2^21+2^122+2*91+2. Its security allowance B/2^127
is just above 0.03125. The Lean proof rounds the weighted success down to 1/28 and obtains
success at least 9801/280000, still strictly greater than B/2^127. This contradicts weak
security and proves that some index costs at least **93 compressions**.

The argument permits all oracle-input collisions, both usable halves, and arbitrarily long
concatenations. Longer hash inputs only increase charged cost. The same fixed attack estimate
fails at 94; this is not a proof that 93 is optimal.

## Certificate and checks

```lean
OptimalOTS.Challenge.DisclosureLower.candidate :
  WholeWordVerificationLowerBound paperParams 93
```

`WholeWordOrigins.lean` derives the origin bound. `DisclosurePatterns.lean` and
`OrderedCounting.lean` prove the combinatorial bound. The `Averaged*` modules establish the
exact attack probabilities and cost contradiction. `Solution.lean` assembles the theorem and
checks that its only axioms are `propext`, `Classical.choice`, and `Quot.sound`.

Exact numerical check: `python3 tools/tune_lower_bound.py --method words --claims 93,94`.
Full build: `cd formal && lake build OptimalOTS Submissions`.
Official pipeline: `python3 verifier/verify.py disclosure-lower --source . --keep`.
The complete library builds (8899 jobs), and the official verifier accepted all three lower
certificates: whole words 93 in 134.6 s, unrestricted DAG 18 in 140.0 s, and generic 1 in 94.2 s.
The contract pin is `911b12369700ac94c668101279c4aa31868f572f7916f14b97198819f49a1b93`.
The two preserved legacy upper certificates also passed. Every official run used
`python3 verifier/verify.py <track> --source . --keep` on the final formal files.
On macOS the official pipeline runs unsandboxed for development; its comparator and Lean
kernel still perform the pinned statement and axiom checks.

| Track | Class | Claim | Official result | Time |
|---|---|---:|---|---:|
| `disclosure-lower` | Whole-word DAGs | 93 | verified | 134.6 s |
| `generic-lower` | Generic algorithms | 1 | verified | 94.2 s |
| `lower` | Unrestricted DAGs | 18 | verified | 140.0 s |
| `upper` | Legacy DAG upper reference | 106 | verified | 184.2 s |
| `disclosure-upper` | Historical partial-disclosure upper reference | 106 | verified | 183.7 s |

Retained official logs, under
`/private/var/folders/7g/qxrr2pgj40s3ykbngr10jkkr0000gn/T/`:

- Whole-word lower: `ots-verify-erc_aaq3/verify.log`.
- Generic lower: `ots-verify-_rh5_3n4/verify.log`.
- DAG lower: `ots-verify-lcfhsboz/verify.log`.
- Legacy DAG upper: `ots-verify-sbotyjsh/verify.log`.
- Historical partial-disclosure upper: `ots-verify-9lkaciam/verify.log`.

Implementation milestone: local commit `8d05b71` on `main`. The protected generic/DAG definitions,
`Submissions/GenericLower`, `Submissions/Lower`, and `Submissions/Upper` are unchanged. Changes are
confined to the new whole-word contract, the third lower challenge and proof, associated metadata,
arithmetic tooling, documentation and website. Nothing was pushed or deployed. The post-commit
hook refreshed localhost, and a live page check confirmed the commit, three lower series,
whole-word rules and preserved Satoshi/Vitalik rows.

All 18 service tests pass. Firefox checks passed for three lower series, the single generic
upper candidate, lower-framework filters, sorting, keyboard tooltips, rules expansion, both
accessible diagrams and narrow-screen scrolling. Rules remain independent of scores. The local
demo refresh preserves IDs and dates and updates only the whole-word demo claims to 94/95/94;
these are explicitly fictional, while this certificate proves 93.

The retained `disclosure-upper` certificate proves the old partial-disclosure model only. Its
16-bit tweaks do not satisfy whole-word syntax, so neither it nor the 106-cost generic adapter
is asserted to be an upper construction in this restricted class. Demo leaderboard entries
remain explicitly illustrative and separate from this checked theorem.
