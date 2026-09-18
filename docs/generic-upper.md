# Generic upper bound

The `generic-upper` track admits arbitrary oracle algorithms with perfect correctness,
signing failure at most `2⁻¹²⁸`, 127-bit strong unforgeability, and the fixed size and resource
limits. Its forest construction verifies within **106 compressions** on every input and
oracle-answer path. All proofs live in `formal/Submissions/GenericUpper/`.

The three lower tracks are unchanged: generic algorithms, unrestricted DAGs, and whole-word
DAGs. The original `Upper` and `DisclosureUpper` roots remain historical reference certificates;
the generic submission is a separate, self-contained root. Historical submissions are not
reclassified as generic records.

## What the challenge requires

A submission chooses an `AlgorithmScheme paperParams`: a secret-key type, a signature type
with injective bit-string encoding, and three terminating oracle programs for key generation,
signing, and verification. There is no required graph, nonce, index query, word size, or
revelation pattern. Deterministic computation and private randomness are free; all programs
share the same bare random oracle and compression-cost model.

`OptimalOTS.Challenge.GenericUpper` exports exactly:

```lean
noncomputable def scheme : AlgorithmScheme paperParams

theorem admissible :
    scheme.Admissible AlgorithmScheme.paperLimits (1 / 2 ^ 128)

theorem secure : scheme.Secure

theorem cost : scheme.VerifyCostAtMost 106
```

The challenge substitutes a submission's claim for 106. `Admissible` requires:

- Perfect correctness: an honest returned signature is rejected with probability zero.
- Signing failure at most `2⁻¹²⁸`, averaged over honest key generation and signing, for every
  message chosen as a function of the public key. This is not availability after adversarial
  oracle preprocessing.
- Signatures of at most 5,504 encoded bits, and rejection of oversized signatures.
- At most 1,024 key-generation compressions and `2²¹` signing compressions on every path.

Public keys are 128 bits and messages are 256 bits. The separate security theorem gives
strict strong-unforgeability probability below `B / 2¹²⁷` for every pathwise budget `B` of the
entire attack experiment, including honest operations and final verification. The verification
cost theorem covers all inputs, including malformed signatures and rejecting paths.

The upper availability threshold is stricter than the generic lower challenge's one-half
allowance, so this upper construction lies within the class covered by the generic lower bound.
Neither the generic model nor any lower statement acquires a graph or separation assumption.

## Correctness proof

The proof establishes correctness for **every DAG adapter**, not just the forest.

Key generation leaves an assignment satisfying every deterministic-node equation and a shared
cache containing every hash-node answer. This holds even when hash inputs coincide. Successful
signing returns the encoding of one disclosure cut and records its index query in that cache.
Subsequent operations only extend the cache, so verification repeats the same index and selects
the same cut.

Decoding recovers every disclosed value. A topological induction over visited nodes recovers
the original assignment: the cut contains every visited source, deterministic nodes obey the
same equations, and hash nodes receive the recorded answers. The reconstructed public key
therefore equals the generated key. This is a statement about every supported execution, so
it also proves probability-zero rejection for every public-key-dependent message choice.

## Signing availability proof

The forest's explicit hash inputs have lengths 144, 400, or 912 bits. Thus its key-generation
cache contains no 512-bit message-and-nonce input. This is a proved property of this construction's
actual bit strings, not an extra oracle label or a condition imposed on generic algorithms.

Signing samples distinct 256-bit nonces. Each resulting 512-bit index query is fresh, including
when the message depends on the public key. Its low 128 answer bits are uniform; `2¹¹⁵` of the
`2¹²⁸` possible indices are accepted. Every trial therefore fails with probability `8191/8192`.
After `2²¹` trials, the failure probability is exactly

```text
(8191 / 8192)^(2^21).
```

The reciprocal Bernoulli inequality gives `(8191/8192)^8192 ≤ 1/2`. Since
`2²¹ = 8192 × 256`, total failure is at most `2⁻²⁵⁶`, hence at most the challenge allowance
`2⁻¹²⁸`. A separate exact-integer check confirms `2 × 8191^8192 ≤ 8192^8192`; the Lean proof,
not the numerical check, certifies the claim.

## Security and resource preservation

`Adapter.lean` wraps the original DAG programs unchanged. The encoded signature is the
256-bit nonce followed by at most 5,248 disclosed bits. Serialization is injective. Translations
of adversaries in both directions establish equality of the generic and DAG oracle experiments
before oracle interpretation. All queries, costs and success probabilities agree exactly;
there is no security loss or extra failure term.

The forest has 63 chains, grouped through a fixed hash tree. Its explicit 16-bit tweaks are
charged in the actual input lengths. The copied security proof establishes all internal
construction properties before proving strong security; the generic challenge imposes none
of those properties on other submissions. The construction uses 912 key-generation compressions,
at most `2²¹` signing compressions, and at most 106 verification compressions.

`Resources.lean` establishes the size, rejection, and pathwise cost bounds.
`CorrectKeygen.lean` and `Correctness.lean` establish correctness. `Availability.lean` establishes
signing availability. `ForestAlgorithm.lean` combines these results, and `Solution.lean` exports
the challenge declarations. `OptimalOTS/AlgorithmForest.lean` provides compatibility aliases.
The original `formal/Submissions/Upper` files are unchanged.

## Verification

```sh
cd formal
lake build OptimalOTS Submissions
lake env lean scripts/check-axioms.lean
cd ..
python3 verifier/check_submission.py generic-upper
python3 verifier/verify.py generic-upper --source .
```

The protected generic definitions are unchanged; their introduction now describes both tracks. The new challenge fixes the allowance and
requires all three proofs; comparator checks those declarations and their shared scheme against
the pinned contract. Permitted axioms remain `propext`, `Classical.choice`, and `Quot.sound`.

The official verifier accepted `generic-upper` at 106 in 157.3 seconds. The complete Lean build
passes (8,927 jobs), all 46 protected model declarations pass the axiom audit, and every submission
root passes policy. The verifier, service, and numerical suites pass 59, 59, and 5 tests respectively;
JavaScript and shell syntax checks also pass.

The contract pin is `b2b1ffdeb02aa410fe2133b6b7e652f6f55ddf357eb0c5cd58dbb877792303b2`
with 22 protected files. The new root contains 30 files and imports no other submission root.
All 20 inherited construction/security modules match the original Upper files exactly except
for sibling import paths. The original Upper root and all three lower statements are unchanged.

Localhost now uses normal generic upper admission, records, chart points and leaderboard rows.
The rules retain the distinct lower and upper availability thresholds. Firefox checks pass on
desktop and at 320/390-pixel widths, in light/dark mode, including keyboard controls, sorting,
filters, tooltips, collapsed rules and both diagrams. All 19 existing demo rows are preserved;
two new, clearly fictional generic upper rows use 106 and 105. Those demo scores are not proof
certificates.

Local artifacts: `/private/tmp/ots-generic-admission-checks.log`,
`/private/tmp/ots-generic-admission-verify-generic-upper.json`, and
`/private/tmp/ots-ui-generic-upper/`. These macOS results establish proof acceptance and local
application behavior; deployment still requires the Linux and staging checks in
[the production review](production-readiness.md).
