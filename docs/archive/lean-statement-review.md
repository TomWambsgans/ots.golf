# Lean statement review — 17 September 2026

Reviewed all 111 project-owned Lean files and challenge templates. The review found no mismatch
between the exported mathematical statements and their intended scope. It corrected misleading
or stale explanations in 37 files. Definitions, hypotheses, conclusions, proof terms, declaration
names and numerical claims are unchanged.

Three parallel reviewers covered generic algorithms, the lower proofs, and the historical upper
proofs; the integration review covered the shared DAG contract and strong-to-weak bridge.

## Coverage

| Area | Files | Main checks |
|---|---:|---|
| Shared DAG contract and security bridge | 2 | Oracle identity, bit order, costs, cuts, security quantifiers |
| Generic interface, adapter and lower proof | 12 | Correctness, availability, serialization, pathwise budgets, zero-query attack |
| Whole-word/origin definitions and both DAG lower roots | 46 | Exact grammar, origin counting, conversion, freshness, attack costs |
| Historical upper roots | 43 | All 1,629 declarations, discharged hypotheses, security and cost exports |
| Challenge templates | 5 | Exact exported types, units, weak/strong security and admission scope |
| Library root, Lake configuration and axiom audit | 3 | Module roles, imports and audit coverage |

Duplicated proof modules were compared after normalizing their import prefixes, with all
differences reviewed. The historical upper roots were reviewed without edits, preserving the
standing instruction not to modify the original upper construction.

## Clarifications made

- **One oracle, full input cost.** Removed a comment about reusing a prefix's compression state:
  that optimization is not part of this random-oracle cost model. Explicit prefixes and repeated
  queries are charged. Public-key truncation keeps the low bits, rather than an unspecified prefix.
- **Strong and weak security.** After successful signing, strong forgery requires a new pair and
  weak forgery a new message. After signing failure, both still require verification to accept.
  The budget covers the entire experiment, including honest-party queries. A weak-security lower
  bound applies to strongly secure schemes; this does not assert equal optima for the two classes.
- **Generic admissibility.** Correctness is zero rejection probability for returned honest signatures.
  Availability is averaged over honest key generation and signing for every public-key-dependent
  message choice, without adversarial preprocessing. The allowance is at most one half, not exactly
  one half. Resource bounds cover every oracle-answer path; verification also covers rejected inputs.
- **Lower-bound quantifiers.** The generic statement bounds every finite verification budget that
  satisfies the contract. It does not assert that every algorithm has such a budget. Its proof
  requires admissibility, weak security and the fixed resource limits. Noncomputable public
  signature selection is deliberate in this model of free deterministic computation.
- **Whole words and origins.** Fixed halves are selected directly from hash nodes. Concatenation
  may reorder, repeat or group earlier values, including an empty list. Disclosures contain complete
  node values. Hash origins follow declared parent edges, even when a deterministic function ignores
  a parent; the 41-origin bound is derived, not an additional admission condition.
- **Proof documentation.** Removed an obsolete attack-cost formula, repaired lemma references, and
  distinguished exact probabilities from lower bounds. Nonce-search comments now specify wrapping
  and the freshness conditions needed by the probability lemmas.
- **Certificate scope.** Challenge comments identify the three lower classes and historical upper
  references correctly. The generic forest adapter proves security and resource bounds; it still
  does not prove generic admissibility or open the generic upper challenge.

## Validation

A nested-comment-aware comparison, preserving string literals, checked all 111 files against the
pre-review commit: every non-comment token stream is identical. Both historical upper roots are
byte-for-byte unchanged. No executable `sorry`, new axiom, `unsafe` declaration or `native_decide`
was introduced. The challenge templates retain their intentional verifier placeholders.

Comment changes in protected files require a new byte-level pin. The updated contract ID is
`137610f30255a344bb9e888f65b470916308db7b2bd40660c5edb22e91edae95`.
This is an editorial update, with identical mathematical declarations.

Validation:

- `lake build OptimalOTS Submissions`: passes, 8,899 build jobs. Existing unused-tactic warnings
  remain; proof scripts were not rewritten for this editorial review.
- `lake env lean scripts/check-axioms.lean`: passes; all 46 audited declarations use only the
  permitted axioms, and no protected module declares an axiom.
- Repository regressions: all 118 tests pass (57 verifier, 56 service, 5 numerical), along with
  JavaScript and shell syntax checks.

The official verifier accepts all five certificates against the updated pin:

| Track | Claim | Result | Reported duration |
|---|---:|---|---:|
| `generic-lower` | 1 | verified | 76.9 s |
| `lower` | 18 | verified | 128.9 s |
| `disclosure-lower` | 93 | verified | 103.4 s |
| `upper` | 106 | verified | 164.0 s |
| `disclosure-upper` | 106 | verified | 151.3 s |

These runs check the mathematical certificates on macOS; they do not replace the Linux production
acceptance checks. Local evidence is in (local log),
`ots-lean-review-axioms.log`, `ots-lean-review-regressions.log`, and
`ots-lean-review-verify-<track>.json` in the same directory. The token comparison script and its
pre-review file manifest are also retained there. No files were pushed or deployed.

## Historical prose retained with the upper roots

The original upper files remain unchanged as requested. Their theorem statements are consistent,
but some surrounding prose is stale: section references and links to a missing `DESIGN.md`, an old
cache-lemma name, and a phrase that all values are 128 bits. In fact, frontier values are 128 bits,
hash outputs are 256 bits, and the tweaked hash inputs have their explicitly declared lengths.
The old README also understates the node count: `Names.N` is 2,795. These comments do not add
hypotheses or affect the certificate; the corrected challenge documentation states its actual scope.
