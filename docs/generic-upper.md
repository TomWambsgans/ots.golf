# Generic upper-track foundation

The generic algorithm interface and the adapter for the existing forest are proved in Lean.
The wrapped forest retains the exact 127-bit strong-unforgeability experiment, verifies within
106 compressions on every input, uses at most 1024 key-generation compressions and `2^21` signing
compressions, and produces signatures of at most 5504 bits.

This is the first step toward generic upper submissions. The pinned contract, challenge stubs,
submission import policy, and both submission roots are unchanged. At that milestone the leaderboard certified DAG schemes with bounds 18 and 106. The later website
structure has three lower-bound classes and only this generic upper track. It labels the 106-cost
adapter as a candidate pending admission; the old DAG upper certificates remain local references.

A later, separate [partial-disclosure framework](partial-disclosures.md) adds DAG schemes with
at most 46 disclosed hash origins and certified bounds 80 and 106. It does not complete the
generic admission requirements below or establish a generic lower bound.

A separate [generic lower theorem](generic-lower.md) now proves at least one compression for every
correct, weakly secure oracle algorithm whose signing succeeds with probability at least one half.
The generic lower track is now open with a pinned challenge and ordinary submission root. This
does not supply the upper adapter's missing correctness or availability proofs. Lower and upper
admission are independent.

## Interface

`formal/OptimalOTS/Algorithm.lean` introduces `AlgorithmScheme P`:

```lean
structure AlgorithmScheme (P : Params) where
  SecretKey : Type
  Signature : Type
  encodeSignature : Signature → List Bool
  encodeSignature_injective : Function.Injective encodeSignature
  keygen : OracleComp (Spec P) (PublicKey P × SecretKey)
  sign : SecretKey → Message P → OracleComp (Spec P) (Option Signature)
  verify : PublicKey P → Message P → Signature → OracleComp (Spec P) Bool
```

There is no graph, disclosure family, required nonce, or required index query. Programs may
branch and choose later queries from earlier answers. They use the same bare random oracle;
private randomness and deterministic computation remain free. This retains the present
mathematical query-complexity model, including noncomputable descriptions, rather than imposing
machine-time bounds or claiming executable implementations.

The signature type is chosen by the scheme. Injective serialization makes its information fit
in the counted wire data: two different signatures cannot hide behind the same bit string.
`SignatureSizeAtMost` bounds every returned signature's encoded length; `RejectsOversized`
requires rejection of larger signatures. Public keys and messages still have the widths
specified by `Params`. The generic programs never use the DAG-specific nonce/index/family
parameters unless the scheme chooses to use them.

`AlgorithmScheme.Secure` quantifies over generic two-stage adversaries, allows the first message
to depend on the public key and oracle queries, and requires

```
CostAtMost P (scheme.experiment attacker) B
  → probTrue P (scheme.experiment attacker) < B / 2^P.securityBits.
```

The cost includes key generation, signing, both attacker stages, and final verification. The
winning condition is unchanged: acceptance of a message/signature pair different from the one
returned by the signer, or any accepted pair when signing failed. At `paperParams`, the exponent
is still 127. `VerifyCostAtMost c` is a pathwise bound for every public key, message and signature,
including rejecting inputs.

## Exact embedding and forest certificate

`AlgorithmAdapter.lean` defines `Scheme.toAlgorithm` with exactly the original three programs.
Its serialization is the fixed-width nonce followed by the disclosed bits. It proves the
serialization injective and gives translations of adversaries in both directions.

For every DAG scheme `S`:

```lean
AlgorithmAdapter.experiment_eq :
  S.toAlgorithm.experiment A = experiment S (AlgorithmAdapter.toDAGAdversary S A)

AlgorithmAdapter.secure_iff : S.toAlgorithm.Secure ↔ S.Secure
```

These are equalities of oracle programs before random-oracle interpretation. They preserve
all queries, every pathwise cost bound, and success probability exactly. There is no additional
failure term or security loss. The equality handles the different decidable-equality instances
at the final winning predicate explicitly.

`AlgorithmCosts.lean` proves structural cost rules and bounds for DAG key generation, signing
and verification in a namespace independent of the submission libraries. Its generic cost
arguments are adapted from the lower proof, without importing either submission root.
`AlgorithmResources.lean` proves size bounds, oversized rejection, and adapter resource bounds.

`AlgorithmForest.lean` is the integration module. It imports the upper baseline's existing
theorems and exports:

```lean
AlgorithmForest.scheme : AlgorithmScheme paperParams
AlgorithmForest.secure : AlgorithmForest.scheme.Secure
AlgorithmForest.cost : AlgorithmForest.scheme.VerifyCostAtMost 106
```

The combined `AlgorithmForest.certificate` additionally proves key-generation cost at most
1024, signing cost at most `2^21`, signature size at most 5504 bits, and rejection of larger
signatures. Its checked axiom closure is exactly `propext`, `Classical.choice`, and `Quot.sound`.
No additional axiom or admitted proof is used. The integration module is outside both submission
roots; it is a checked adapter of the existing baseline, not a newly accepted generic challenge.

## What remains before admitting generic upper submissions

Security alone does not establish that an algorithm is a useful signature scheme. The interface
therefore also defines `Correct`, `SigningFailureAtMost`, and `Admissible` independently of security.
Correctness rules out verification failures when honest signing returns a signature. Availability
bounds the probability of `none` after honest key generation. Both permit the message to be any
function of the public key. Availability after arbitrary adversarial oracle preprocessing is not
asserted by this definition.

The forest's correctness and signing-failure bound have **not** been proved against these new
predicates in this foundation step, so no `AlgorithmForest.scheme.Admissible` certificate is
claimed. Before changing the actual upper challenge:

1. Choose and pin a suitably small upper signing-failure allowance and finalize its message-selection
   semantics. The parameter `ε < 1` in the interface is only a placeholder for that contract choice.
2. Prove correctness and the chosen availability bound for the forest, obtaining an admissible
   baseline at 106 in the generic interface.
3. Build on the generic definitions now pinned for lower, adapt the upper challenge/import policy/comparator declarations,
   and retain the current DAG lower statement.
4. Update the site's track descriptions: a lower bound for DAG schemes need not bound generic
   algorithms. A generic result below 18 would not contradict the existing lower theorem.

## Validation

The focused command is `cd formal && lake build OptimalOTS.AlgorithmForest`. The module's
`#guard_msgs` checks the combined certificate's permitted axiom closure.

Completed checks:

- `lake build OptimalOTS.AlgorithmForest`: passed.
- `lake build OptimalOTS Submissions`: passed (8842 jobs).
- `python3 verifier/pin_contract.py check`: passed; the pin remains `9564de9198acd655`.
- Both submission-policy checks passed at lower 18 and upper 106.
- Both submission roots, the statement, challenge metadata, and pin are unchanged from `main`.
- `git diff --check`: passed.

Official regression results (`python3 verifier/verify.py <track> --source . --keep`):

```text
verified: track=lower claim=18 commit=worktree in 118.2s
verified: track=upper claim=106 commit=worktree in 167.8s
```

Logs:

- Lower: `/private/var/folders/7g/qxrr2pgj40s3ykbngr10jkkr0000gn/T/ots-verify-pq9racsp/verify.log`.
- Upper: `/private/var/folders/7g/qxrr2pgj40s3ykbngr10jkkr0000gn/T/ots-verify-hoziuc6i/verify.log`.

These official runs check the existing challenge exports. The new adapter certificate is checked
by the Lean build and its axiom guard; it is not yet an export accepted by the competition verifier.
