# Upper bound: arbitrary oracle algorithms

The `generic-upper` track admits arbitrary oracle algorithms with perfect correctness,
signing failure at most `2⁻¹²⁸`, 127-bit strong unforgeability, and the fixed size and resource
limits. Its forest construction verifies within **106 compressions** on every input and
oracle-answer path. All proofs live in `formal/Submissions/GenericUpper/`.

The three lower tracks are Generality 3/3 (any algorithm), 2/3 (DAGs) and 1/3 (whole-word DAGs).
The original `Upper` and `DisclosureUpper` roots remain historical reference certificates.

## What the challenge requires

A submission chooses an `AlgorithmScheme paperParams`: a secret-key type, a signature type
with injective bit-string encoding, and three terminating oracle programs for key generation,
signing, and verification. Deterministic computation and private randomness are free; all programs
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

- Perfect correctness: whenever honest signing returns a signature, verification accepts with
  probability one.
- Signing failure at most `2⁻¹²⁸`, averaged over honest key generation and signing, for every
  message chosen as a function of the public key, starting from a fresh oracle.
- Signatures of at most 5,376 encoded bits, and rejection of oversized signatures.
- At most 1,024 key-generation compressions and `2²⁰` signing compressions on every path.

Public keys are 128 bits and messages are 256 bits. The separate security theorem gives
strict strong-unforgeability probability below `B / 2¹²⁷` for every pathwise budget `B` of the
entire attack experiment, including honest operations and final verification. The verification
cost theorem covers all inputs, including malformed signatures and rejecting paths.

Both algorithm challenges fix signing failure at most `2^-128`. The upper construction lies
within the class covered by the generic lower bound.

## Correctness proof

The proof establishes correctness for **every DAG adapter**.

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

The forest's key-generation queries have lengths 144, 400, or 912 bits. Every 384-bit
message-and-nonce query is therefore fresh after key generation.

Signing samples distinct 128-bit nonces. Each resulting 384-bit index query is fresh, including
when the message depends on the public key. Its low 128 answer bits are uniform; `2¹¹⁵` of the
`2¹²⁸` possible indices are accepted. Every trial therefore fails with probability `8191/8192`.
After `2²⁰` trials, the failure probability is exactly

```text
(8191 / 8192)^(2^20).
```

The reciprocal Bernoulli inequality gives `(8191/8192)^8192 ≤ 1/2`. Since
`2²⁰ = 8192 × 128`, total failure is at most `2⁻¹²⁸`, exactly the challenge allowance. The Lean
proof certifies this bound. A separate exact-integer check confirms
`2 × 8191^8192 ≤ 8192^8192`.

## Security and resource preservation

`Adapter.lean` wraps the original DAG programs unchanged. The encoded signature is the
128-bit nonce followed by at most 5,248 disclosed bits. Serialization is injective. Translations
of adversaries in both directions establish equality of the generic and DAG oracle experiments
before oracle interpretation. All queries, costs and success probabilities agree exactly.

The forest has 63 chains, grouped through a fixed hash tree. Its explicit 16-bit tweaks are
charged in the actual input lengths. The copied security proof establishes all internal
construction properties before proving strong security. The construction uses 912 key-generation compressions,
at most `2²⁰` signing compressions, and at most 106 verification compressions.

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

At the original admission milestone, the official verifier accepted `generic-upper` at 106 in
157.3 seconds. The complete Lean build
passes (8,927 jobs), all 46 protected model declarations pass the axiom audit, and every submission
root passes policy. The verifier, service, and numerical suites pass 59, 59, and 5 tests respectively;
JavaScript and shell syntax checks also pass.

That milestone used contract pin `b2b1ffdeb02aa410fe2133b6b7e652f6f55ddf357eb0c5cd58dbb877792303b2`
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

All six configured official certificates pass against the same pin: generic upper 106, generic
lower 1, DAG lower 18, whole-word lower 93, and both historical upper references at 106. Timings
and regression evidence are recorded in [the production review](production-readiness.md#generic-upper-admission-update).

Two deliberate negative submissions also compiled successfully and were then rejected by
comparator's statement matching: changing only the claim to 105 was rejected at `cost` (127.2 s),
and replacing the admissibility theorem's fixed `2^-128` allowance with a proved one-half allowance
was rejected at `admissible` (120.0 s). The latter leaves security and cost unchanged, confirming
that availability is enforced independently. The test copies were outside the repository.
Results are in `/private/tmp/ots-generic-admission-reject-claim-105.json` and
`/private/tmp/ots-generic-admission-reject-failure-half.json`.
