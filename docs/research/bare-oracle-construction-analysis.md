# The proposed construction bound is false in fresh coordinates

Date: 2026-09-17. This note checks the first open step in section 4 of
the bare-oracle handoff (since removed). It concerns the attempted transfer of paper
Lemma 3 to the bare oracle, not the truth or falsity of the desired lower bound.

The transfer fails at its conclusion, not only at the intermediate assertion
about oracle entropy. The fresh-coordinate weights proposed in the handoff can
give a target weight zero although one construction attempt has positive failure
probability. The counterexample below has exact probabilities at the paper's
256-bit hash width.

## A four-node counterexample

Let `K = 2^256`. Use these nodes in topological order:

1. `z`: a uniformly random one-bit source `Z`.
2. `h`: the hash `H(Z)`, with 256-bit output.
3. `g`: the hash `H(Z)`, with 256-bit output.
4. `r`: the root hash `H(Y_g)`, with 256-bit output.

The queries at `h` and `g` are identical. Root queries have length 256 and the
other two queries have length 1, so they cannot coincide. The unused hash `h` is
permitted by the contract: a graph is not required to have every node reach its
root.

Take the observed disclosure set to be `A_i = {g}` and the target to be
`A_j = {z}`. Both are valid cuts and exclude the root. Then

```
E_i = {r}
E_j = {g,r}
J = E_j \ E_i = {g}.
```

Every hash costs one compression, so key generation costs 3, and the two
verification costs are 2 and 3. The revealed lengths are 256 and 1. These meet
all corresponding contract constraints. A family indexed by `Fin (2^115)`
is obtained by assigning `{g}` to index zero and `{z}` to every other index.
The scheme is not secure, which is immaterial: the proposed construction lemma
is asserted for all schemes before security is used to derive a contradiction.

## Fresh records and their posterior

The proposed fresh record is

```
(Z, U_h, U_g, U_r),
```

with the three `U` values independent and uniform in a set of size `K`.
The deterministic fresh-to-real map is exactly

```
Y_h = U_h,     Y_g = U_h,     Y_r = U_r.
```

Fix any observed revealed output `v` and reconstructed root output `w`.
The observations say precisely `U_h = v` and `U_r = w`. Their probability is
`K^-2 > 0`. The uniform fresh posterior therefore has:

* `Z` uniform on its two values;
* `U_h = v`;
* `U_g` still independent and uniform on all `K` values;
* `U_r = w`.

Consequently the handoff's proposed weight at the only checked node is

```
h_i(g) = 256 - H(U_g | Z,U_h) = 0.
```

The constrained 256-bit coordinate is the coordinate of the hidden hash `h`,
whose weight is 256. It does not belong to `J`.

## Exact success probability

The construction attempt samples a fresh candidate, so its query input is a
uniform bit `z'`. It queries `H(z')`. The candidate filter retains a record
exactly when the answer is `v`, because every candidate's actual output at `g`
equals `U_h = v`. When that answer is `v`, candidates with the sampled source
remain; otherwise the working set becomes empty. Thus, for any fixed oracle,

```
p(H) = |{z' in {0,1} : H(z') = v}| / 2.
```

Conditional on the observations, the true source is uniform. Its answer is
pinned to `v`; the answer at the other one-bit input is independently uniform
on `K` values. Conditioning on the root answer `H(v) = w` has no effect on
either one-bit oracle entry because the query lengths differ. Therefore

```
Pr[p(H) = 1   | observations] = 1/K,
Pr[p(H) = 1/2 | observations] = 1 - 1/K.
```

It follows exactly that

```
E[-log2 p(H) | observations] = 1 - 2^-256 > 0 = h_i(J).
```

This disproves the proposed bare-oracle analogue of paper equation
`(log-success)`. It also disproves the proposed repeated-attempt conclusion:
for every finite positive number `q` of independent attempts, the failure
probability is exactly

```
(1 - 2^-256) * 2^-q > 0,
```

whereas the claimed bound with `d = 0` requires success probability one.

As an independent finite enumeration check, for output alphabet sizes
`K = 2,4,8,16`, enumeration of `(Z,H(0),H(1))` conditional on `H(Z)=0`
gives probabilities of `p=1/2` equal to `1/2,3/4,7/8,15/16`, respectively;
the remaining mass is at `p=1`. These are the exact rational values above.

## The problem does not depend on dead nodes

To make every node reach the root, insert a deterministic node
`b = lowBit(Y_h)` after `h` and replace the root input by `b ++ Y_g`.
The root query then has length 257. Use

```
A_i = {b,g},       A_j = {b,z}.
```

The signing cut has 257 revealed bits; the target cut has 2. Every node is
on a source-to-root path, both cuts are valid, and again
`E_i = {r}`, `E_j = {g,r}`, `J = {g}`. An observed value at `g` already fixes
`b`; hence the same posterior, zero target weight, and exact failure law hold.
All oracle queries still cost one compression.

Thus pruning nodes that do not reach the root does not repair the statement.
No index-oracle collision is involved. Separating the index oracle for the
analysis also does not repair the statement.

## What the existing abstract Lean lemma does establish

`Construction.sum_neg_logb_attemptProb_le` is valid under its actual interface:
each checked node has its own table, and the joint distribution is uniform over
candidate/table pairs consistent at exactly the checked nodes. The proof uses
`card_tables_consistent` to give every candidate the same number of consistent
tables. Nothing in the counterexample contradicts that theorem.

In the bare model, the true posterior contains consistency conditions from
hidden nodes too, and a checked node's fresh coordinate can be a wholly unused
dummy variable. Substituting the true bare law into that existing theorem is
therefore unjustified. Changing only the count of distinct checked inputs does
not fix the mismatch.

## Potential repairs and the remaining barrier

One can restore a useful charge for this particular example by assigning the
weight of the hidden first occurrence to the checked occurrence, or by mapping
the checked node to its collision class. Neither change currently supplies the
two global properties required by paper Lemmas 2 and 4:

1. a total weight controlled by the revealed length, with the desired tail;
2. for every disclosure index, a fixed set of at most `a` weighted objects
   containing the charges needed for its construction attempt.

Simply charging every occurrence the deficit of its actual output can duplicate
one piece of information many times. For example, let `h_1,...,h_t,g` all hash
the same source; reveal one bit of each `h_k` and all 256 bits of `g`, and make
the root depend on that revealed tuple. Each `h_k` has actual-output entropy
deficit 256 after `g` is observed, whereas the revealed length is only `t+256`.
For each `k`, a valid target can reveal the source and the other supplied
values and recompute just `h_k` and the root. A single chosen node representative
does not belong to all these syntactic target sets.

Passing to collision classes handles guaranteed equalities such as these. In a
general bare graph, however, the class partition is a function of the secret
record, including hidden oracle answers. For instance, replace the target input
by `Z` on one secret selector value and by a different input on the other.
The target's representative is then record-dependent. The class image of
`E_j` still has at most `|E_j|` members for each fixed record, but the attacker
does not know that record or the class partition. Conditioning the analysis on
the actual hidden partition does not give an implementable ranking strategy
for free. The counting theorem currently uses a common, fixed node universe
and fixed target sets, while its weights and the attacker's ranks are computable
from the observations alone.

A repair needs a new theorem relating those hidden, record-dependent classes
to an observation-dependent attack, or another weight/attack design. This note
does not prove that no such repair exists. It establishes that the handoff's
proposed construction lemma, and therefore its suggested direct port yielding
24, cannot be used as stated. Numerical slack and the proposed Bell factor do
not change this counterexample.
