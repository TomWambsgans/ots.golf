# Lower bound 80 for partial disclosures

`Solution.lean` exports
`OptimalOTS.Challenge.DisclosureLower.candidate : DisclosureVerificationLowerBound paperParams 46 80`.
This is a bound for all weakly secure schemes whose disclosed payload has at most 46 hash origins.
It does not assert the unrestricted DAG lower bound is 80.

`OrderedCounting.lean` bounds finite families of ordered sets by Pascal's recurrence, using
the largest difference between two members as a boundary witness. `DisclosurePatterns.lean`
proves that this witness is a hash origin of the other disclosure. If every verification costs
at most 79, at most 77 nonroot hash nodes are recomputed and the number of patterns is at most
`Nat.choose 123 46`.

The `Averaged*` modules give a search bound depending on each pattern class's size, prove the
exact weighted signing law, and average over classes using Cauchy–Schwarz. The new-message
forgery succeeds with probability at least 33/1000, above the security allowance for its entire
experiment. The proof uses the actual bare oracle and shared cache, including colliding inputs.

The remaining modules are copies of the unrestricted lower proof's supporting development,
with imports confined to this root. They include free signature conversion between equal
reconstructed hash sets, fresh-message probabilities and complete query-cost bounds. Keeping
them here makes the submission self-contained under the flat-root import policy.

Build: `cd formal && lake build Submissions.DisclosureLower.Solution`.
Official verifier: `python3 verifier/verify.py disclosure-lower --source .`.
The candidate's in-file axiom guard permits only `propext`, `Classical.choice`, and `Quot.sound`.
