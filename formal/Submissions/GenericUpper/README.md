# Generic upper: 106 compressions

A self-contained generic-algorithm submission wrapping the 63-chain forest. The key-generation,
signing, verification, and security experiment are unchanged from the historical construction.
The generic challenge additionally requires perfect correctness and signing failure at most
`2^-128`; the availability proof establishes the stronger bound `2^-256`.

`Solution.lean` exports the scheme, admissibility, 127-bit strong security, and a verification
budget of 106 covering every input and oracle-answer path. All proofs use only `propext`,
`Classical.choice`, and `Quot.sound`.

## Construction

The graph has 2,795 nodes: 63 chains grouped into 21 groups, seven subtrees, and one root.
Hash inputs include explicit 16-bit tweaks, charged in their complete lengths: 144, 400, or
912 bits. Key generation costs 912 compressions. A signature carries a 128-bit nonce and at
most 5,248 disclosed bits. Signing tries at most `2^20` distinct nonces; verification hashes
the 384-bit message-and-nonce input and reconstructs the selected cut within 105 further
compressions.

Those graph properties describe this construction. Other generic submissions may use any
oracle algorithms satisfying the challenge; no DAG, nonce format, or separation condition
is imposed on them.

## Proof map

- `Adapter.lean`: injective serialization and exact equality of security experiments.
- `AlgorithmCosts.lean`, `Resources.lean`: pathwise cost, wire size, and oversized rejection.
- `KeygenSupport.lean`, `Correctness.lean`: cache consistency and correctness of every DAG adapter.
- `Availability.lean`: fresh index queries, exact repeated-failure probability, and its bound.
- `Main.lean` and its siblings: the construction and its original strong-security proof.
- `ForestAlgorithm.lean`: admissibility, security and cost of the wrapped scheme; `Solution.lean`: the required exports.

Imports stay within this root and the allowed protected contract/library modules. The original
`Submissions/Upper` root is unchanged. Run from the repository root:

```sh
python3 verifier/check_submission.py generic-upper
python3 verifier/verify.py generic-upper --source .
```
