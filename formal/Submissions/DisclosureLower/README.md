# Lower bound 93 for whole-word DAGs

`Solution.lean` exports
`OptimalOTS.Challenge.DisclosureLower.candidate : WholeWordVerificationLowerBound paperParams 93`.
The retained track/root names are historical; the challenge now covers every secure DAG
satisfying `Graph.WholeWords`, with no extra provenance or separation assumption.

The protected syntax in `OptimalOTS/WholeWords.lean` permits independent 128-bit sources,
256-bit hashes, selecting a fixed output half, and concatenation of any number of earlier
whole-word values. Signatures disclose complete values. The original DAG experiment, costs,
nonce, cuts and resource limits remain unchanged.

`WholeWordOrigins.lean` proves that 128 times the number of hash origins of a node is at most
its width. Summing over the disclosed payload derives `DisclosureBound 41` from 5248 bits.
`DisclosurePatterns.lean` and `OrderedCounting.lean` bound reconstruction patterns by
`Nat.choose 131 41` if every verification costs at most 92 (90 nonroot hashes).

The `Averaged*` modules prove the signing law, the repetition-class search bound and its
Cauchy–Schwarz average. With two freshness factors of 99/100, the fresh-message forgery succeeds
with probability at least 9801/280000. Its complete experiment costs at most
1024 + 2^20 + 2^122 + 2*91 + 2, contradicting 127-bit weak security. Equal oracle inputs share
answers throughout; deterministic concatenations and either output half introduce no labels.

Build: `cd formal && lake build Submissions.DisclosureLower.Solution`.
Official verifier: `python3 verifier/verify.py disclosure-lower --source .`.
The candidate's axiom guard permits only `propext`, `Classical.choice`, and `Quot.sound`.
