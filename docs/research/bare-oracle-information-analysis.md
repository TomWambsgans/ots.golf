# Information-bound audit for the bare oracle

This is a mathematical audit, not a lower-bound certificate. The proposed Bell-number
correction in the handoff is false for its stated fresh-coordinate weights.

## What the fresh-coordinate representation actually proves

Let the independent coordinates be the source strings `Z` and one uniform 256-bit string
`U_g` per hash node, in graph order. At node `g`, reuse the answer of the first earlier
query with the same entire input string, if any; otherwise use `U_g`. This deterministic
map has exactly the bare-oracle key-generation law: a fresh query receives an independent
uniform answer and a repeated query receives its cached answer.

For an observation `o` comprising a disclosure and its reconstruction transcript, the
preimage of `o` in this independent product space has a uniform posterior `Q_o`. Thus this
representation does fix the nonuniform-record issue. It does not give the other claims
in the handoff for free.

Put `d_g = 256 - H_Q(U_g | Z,U_<g)`. If the input at `g` repeats, `U_g` is unused by the
entire evaluation and observation. Conditional on any such prefix, it stays uniform.
But “`g` repeats” need not be constant on the posterior, so the unconditional number
`d_g` is not automatically zero merely because `g` repeats in the actual record.

When `g` is reconstructed, its actual answer is observed. Conditional on a prefix where
`g` is fresh, `U_g` is therefore fixed; on a prefix where it repeats, `U_g` remains uniform.
Consequently

```
d_g = 256 Pr_Q[g is a first occurrence]                 (g in E),
sum_(g notin E) d_g
  <= -log2 Pr[o] - 256 E_Q[number of first occurrences in E].
```

The expectation is essential unless that number is determined by the observation.

## Counterexample to the Bell correction

Choose a public constant bit string `a`. Use four nodes, in this order:

1. `p`: a deterministic node with no parents, whose value is `a`;
2. `h`: the hash `H(p)`;
3. `q`: another deterministic node with no parents, whose value is `a`;
4. `r`: the root hash `H(q)`.

Give every index the empty disclosure set. This is allowed by the exact contract:
there are no sources, so the source-to-root cut condition is vacuous; the root is not
disclosed; key generation costs two compressions if `a` is at most 512 bits. Unused
nodes are expressly allowed (audit finding F1).

Reconstruction evaluates only `r`, so `E = {r}` and the disclosure length is zero.
In fresh coordinates, `Y_h = U_h` and `Y_r = U_h`; the coordinate `U_r` is never used.
Observing the reconstructed root `v` fixes `U_h=v`. Therefore

```
d_h = 256,  d_r = 0,  sum_(g notin E) d_g = 256
```

with probability one. For example, at `u=1`, the proposed bound would read
`1 <= Bell(1) * 2^-1 = 1/2`.

There are no two reconstructed nodes to collide: the partition of `E` has one block
and only one possible value. The problem is that a reconstructed query first occurred
at a hidden node. Partitioning only by collisions *inside* `E` cannot repair this.
This scheme is insecure, but the proposed information lemma was unconditional. No
argument excluding precisely this obstruction from secure schemes has been supplied.

A safe consequence of product-space counting alone is the much weaker tail budget
`disclosure length + 256|E| + u`, because the full observation has at most that many
bits before the slack `u`. That does not resolve the construction-bound obstruction
found separately in [the construction analysis](bare-oracle-construction-analysis.md).

## A different route: repeated reconstruction patterns

The following records the initial entropy-free proposal for a lower bound of 18. Its independent
index-oracle argument was subsequently replaced by the direct cache argument in the next section,
and that complete replacement is now formalized and officially verified.

Assume all verification costs are at most 17. Let `E_i` be the reconstructed hash nodes,
including the root, and `V_i = E_i \ {root}`. Since the index and root each cost at least
one compression, `|V_i| <= 15`. There are at most 1024 hash nodes in the whole graph,
so there are at most 1023 nonroot hash nodes. Thus the number `N` of distinct patterns
`V_i` is bounded by

```
N <= sum_(k=0)^15 choose(1023,k) < 2^110.
```

The logarithm of this exact integer sum is approximately 109.60152042072887.
There are `M=2^115` indices. At most `7N`, and certainly at most `8N <= M/4`, indices
can lie in pattern classes of size below eight. Consequently a uniformly selected
index belongs to a class of size at least eight with probability at least three quarters.

Given an honest disclosure at `i`, reconstruct it and retain the complete input/output
pairs at `E_i`. Enumerate graph records consistent with its disclosed values and those
reconstructed outputs, treating source strings and hash outputs as finite freely chosen
values, and requiring deterministic consistency. The actual record witnesses nonemptiness.
Choose any such record. Induction through the reconstruction proves that its query inputs
at `E_i` are exactly the observed inputs. For any `j` with `E_j=E_i`, its disclosure at
`j` therefore reconstructs correctly under the actual oracle, without any further node
queries to construct it. This step does not require a uniform posterior or independence.

In an experiment with an independent index oracle, the signed index is uniform, and
searching `T=2^122` fresh nonces of another message hits a class of size at least eight
with probability at least

```
1 - (1 - 8/2^128)^T >= 1 - exp(-1/8) > 1/9.
```

The final strict inequality follows from `exp(1/8) > 1 + 1/8 = 9/8`.
Allowing signing failure at most `2^-256`, total success is greater than
`(1-2^-256)/12` before the node/index collision correction. Its total query budget is
at most `2^122 + 2^20 + 1024 + 2*17`, comfortably below `2^123`, whose security threshold
is `1/16`. Drawing the two distinct messages uniformly gives a negligible correction
for node/index collisions, since this attack makes only about 1056 node-role queries.
The adaptive independence needed for that last sentence still needs its own explicit
coupling proof; it is not implied just by writing down the numerical union bound.

This route avoids both false entropy lemmas. It does not establish 24. At size 16 the
same pattern count exceeds `2^115` (its log2 is approximately 115.58027394383527), so the
argument as written stops at 18.

## Direct bare-oracle probability argument for the pattern attack

The replacement avoids an independent index oracle entirely. Condition on any key-generation
outcome and its cache. The cache has at most 1024 entries because every hash query costs at least
one. A uniformly sampled 256-bit message has its entire nonce domain disjoint from that cache
unless it equals the message prefix of a cached 512-bit string. There are at most 1024 such
prefixes, so the probability of full freshness is at least `1-1024/2^256 > 9/10`.

For any fixed fresh message, each signing trial is fresh, including after conditioning on all
previous failed trials, because the signer never retries a nonce. If `G` is the good set of
indices (pattern-class size at least eight), the probability of a returned index in `G` is
exactly `(G.card/M)*(1-(1-M/2^128)^L)`. Here `G.card/M >= 3/4`. The elementary inequality
`(1-p)^L <= 1/(1+L*p)` gives failure at most `1/257`; hence signing selects `G` with probability
at least `1/2`. This law does not require independence from the hidden graph once the initial
cache is fixed and the message's nonce domain is fresh.

Condition next on any such signed outcome. Its cache has at most `1024+2^20` entries.
Reconstructing the honest disclosure only repeats cached key-generation queries. Sample a
second uniform message now, independently of this whole outcome. Its full nonce domain is
fresh and it differs from the first message with probability at least
`1-(1024+2^20+1)/2^256 > 9/10`. Search the first `T=2^122` distinct nonces of this message.
For a class of size at least eight, the chance of finding a class index is at least
`1-(1-8/2^128)^T >= (T*8/2^128)/(1+T*8/2^128) = 1/9`.

Convert the signed disclosure to that target by the deterministic candidate procedure.
The verifier repeats already cached queries and accepts. The messages differ, so this wins
`weakExperiment`. Multiplication of the conditional lower bounds gives success at least
`(9/10)*(1/2)*(9/10)*(1/9) = 9/200`.
The whole pathwise budget is `B=1024+2^20+2^122+34` (two index queries beyond the search,
and two reconstructions of cost at most 16). Exact arithmetic gives `B/2^127 < 1/25 < 9/200`.

This settles the probability argument without the adaptive coupling gap mentioned in the initial
exploration above. The full attack is now formalized in `Submissions/Lower/PatternAttack.lean`
and `PatternAssembly.lean`; `Solution.lean` exports `VerificationLowerBound paperParams 18`.
The final official lower verifier accepted claim 18 in 117.5 seconds, with only the three
allowed axioms. See [the final report](../archive/bare-oracle-lower-report.md) for the final checks.
