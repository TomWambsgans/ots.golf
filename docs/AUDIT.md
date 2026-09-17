# Audit of the bare-oracle contract

Scope: `formal/OptimalOTS/Statement.lean`, its VCVio cost/oracle definitions, and the
submission certificates. Updated 2026-09-17 for the bare single-oracle branch.
The contract exposes only bit strings as oracle queries. The verified baselines
are lower 18 and upper 106. The official lower verifier accepted claim 18 in
89.5 seconds on this branch. The lower proof uses repeated reconstruction
patterns; it does not transfer the former labeled-model entropy argument.

## What is trusted

| Component | Pinned at | Role |
|---|---|---|
| Lean 4 | `formal/lean-toolchain` (v4.33.1) | kernel checking every claim |
| Mathlib, VCVio and dependencies | `formal/lake-manifest.json` | definitions used by the statement |
| leanprover/comparator | `c0c5a52d` | statement matching, axiom checking, kernel replay |
| lean4export | `15f6055e` (v4.33.0) | export of declaration dependencies |
| landrun + systemd (Linux verifier) | `811cfff5` | build isolation |

Submission proofs are checked by the kernel. Their permitted axioms are only
`propext`, `Classical.choice` and `Quot.sound`.

## Contract semantics

`CostAtMost` uses VCVio's `IsQueryBound`: a pure computation satisfies any budget;
a query is permitted when its cost is at most the remaining budget, and every
continuation must satisfy the remaining budget after subtraction. Thus the
budget covers every execution path, including branches with negligible
probability. Private uniform sampling is free.

The oracle implementation is `uniformSampleImpl.withCaching`. Its cache key is
`Query := Σ k, BitVec k`: the full length and bits, with no role or node label.
The first query to a string gets a uniform 256-bit answer; all later queries to
that string get the cached answer. Hash-node inputs can coincide with each other
or with message-and-nonce inputs. Such outputs are not independent uniform
record coordinates. No graph separation hypothesis is part of the contract.

| Contract feature | Lean declaration | Audit note |
|---|---|---|
| One random oracle on bit strings | `Query`, `hashSpec`, `oracleImpl` | length is part of a string's identity |
| Cost per started 512-bit block, at least one | `blockCost`, `queryCost` | every bit in an explicit tweak is charged |
| Sources, arbitrary deterministic nodes, hash nodes | `NodeKind`, `Graph` | hash nodes have one parent and no label |
| Root is a hash node | `Graph.root_isHash` | root is never disclosed |
| Key generation evaluates all nodes, within 1024 compressions | `Graph.keygen`, `Scheme.keygen_le` | |
| Disclosure sets cut every source-to-root path | `root_not_mem`, `no_hidden_source` | |
| Reconstruction stops at disclosed values | `Graph.Visited`, `evaluated`, `reconstruct` | root is always evaluated |
| Verification cost is index plus reconstruction | `Scheme.verifyCost`, `idxCost` | the 512-bit index input costs one compression |
| Index is low 128 bits of `H(m ‖ η)` | `index`, `setWidth idxBits` | the same oracle handles node inputs |
| Signing samples distinct nonces, at most `2^21` trials | `Scheme.sign`, `signLoop` | fresh nonces need not be fresh oracle strings |
| Public key is low 128 bits of the root | `publicKey`, `Scheme.verify` | |
| Strong forgery differs from the received pair | `experiment`, `Scheme.Secure` | any accepted pair wins when signing fails |
| Weak forgery uses a different message | `weakExperiment`, `Scheme.WeaklySecure` | hypothesis used by the lower track |
| Security requires `Pr[Forge] < B/2^127` for every valid budget | `CostAtMost`, `Secure`, `WeaklySecure` | includes keygen, signing and final verification |
| Unconditional lower certificate | `VerificationLowerBound paperParams 18` | repeated reconstruction patterns and a forgery on a different message |

`formal/OptimalOTS/Weak.lean` proves that strong security implies weak security.
The lower certificate therefore applies to every secure scheme and also to
schemes permitting malleability of a signature on the signed message.

## Certificate status and open proof work

The lower certificate proves 18 for every weakly secure scheme. Under the contrary
assumption that every verification costs at most 17, each reconstruction uses at
most 15 non-root hash nodes among at most 1023. There are fewer than `2^110`
possible such node sets. Most of the `2^115` indices therefore lie in classes of
at least eight indices with the same reconstruction pattern. A deterministic
candidate construction converts a valid signature to any index in its class.

The attack samples messages uniformly to avoid previously queried message-prefix
domains, then tests `2^122` distinct nonces for its new message. Its proven success
is at least `9/200`; its total cost is at most
`1024 + 2^21 + 2^122 + 34`, whose ratio to `2^127` is smaller than `9/200`.
This contradicts weak security. No assumption about distinct hash inputs or
independent node outputs is used. The elementary index-plus-root bound 2 remains
available as a separate lemma.

The upper certificate remains 106. Its concrete scheme prepends a 16-bit tweak
to every node input; those bits are included in the charged input lengths (144,
400 and 912 bits). This is a choice made by that scheme, not a restriction on
schemes considered by the lower theorem.

The former lower bound 25 relied on distinct oracle labels. Two proposed
fresh-coordinate replacements fail in the bare model. An earlier hidden hash
can query the same string as a later reconstructed hash, placing the information
weight outside the reconstructed set; the corresponding construction bound can
also charge outside its target set. A Bell-number correction does not repair
these counterexamples. Details:

- [Information analysis](bare-oracle-information-analysis.md).
- [Construction analysis](bare-oracle-construction-analysis.md).
- [Conditional numerics](bare-oracle-numerics.md): the simple proposed-24 point has
  numerical slack, but its missing mathematical hypotheses prevent certification.
- [Current port status](bare-oracle-port.md) and [proof map](lower-bound-proof.md).

The repeated-pattern proof establishes 18. Bounds 19 through 25 remain open in
the bare model. In particular, the number of subsets of at most 16 non-root hash
nodes already exceeds `2^115`, so the same counting argument does not directly
prove 19. Conditional numerical searches do not establish a stronger bound.

## Model details retained

- The graph need not have a unique sink, and nodes need not reach the root.
  Verification follows the root's dependencies; other nodes still consume
  key-generation or disclosure budgets.
- An empty hash input costs one compression.
- `sampleAssignment` samples values for all nodes, but only source samples are
  used. Sampling is free.
- Index and public-key truncation use the low bits, matching `setWidth`.
- The adversary's other computation and private randomness are unbounded and free.
- The secure upper certificate establishes non-vacuity of both security classes.

## Contract changes and verification

Protected files are pinned by `verifier/protected.sha256`. Changes to the oracle
model or baseline metadata require re-pinning and official verification of both
tracks. The bare-oracle branch is a contract revision in development; these
notes do not claim a production deployment or leaderboard promotion.
