# Audit of the contract (draft v1)

Scope: `formal/OptimalOTS/Statement.lean` against Section 2 of the paper, the VCVio definitions
it relies on (commit `25f26bf`), and the toolchain it is checked with. Date: 2026-09-16.
Result so far: no soundness issue found; six harmless generalizations documented; one item open
until the upper baseline is verified (F7).

## What is trusted

| Component | Pinned at | Role |
|---|---|---|
| Lean 4 | `formal/lean-toolchain` (v4.33.1) | the kernel that accepts every claim |
| Mathlib, VCVio and their dependencies | `formal/lake-manifest.json` | definitions the statement is built from |
| leanprover/comparator | `c0c5a52d` (declared toolchain 4.33.0, built on 4.33.1) | statement match, axiom check, kernel replay |
| lean4export | `15f6055e` (tag v4.33.0, comparator's own pin) | export of the closure of the named declarations |
| landrun + systemd (Linux verifier) | `811cfff5` | keeps the submission's build off the network and off the trusted files |

Everything else, including the baseline proofs and every submission, is checked by the kernel
and needs no trust.

## Checks performed

1. Line-by-line comparison of the statement with the paper (table below).
2. The two VCVio definitions carrying the cost model and the oracle:
   `IsQueryBound oa B canQuery cost` unfolds to `PFunctor.FreeM.IsRollBound`: `pure` satisfies any
   bound, and `query t >>= k` satisfies it when `canQuery t B` and every continuation satisfies it
   at `cost t B`. With `canQuery := queryCost ≤ ·` and `cost := · − queryCost` this is "total cost
   at most B on every execution path", including all branches. `randomOracle` is
   `uniformSampleImpl.withCaching`: a uniform answer on the first query, cached under the full
   query, which is the label together with the input length and bits.
3. `formal/scripts/check-axioms.lean`: the 18 declarations that fix a certificate's meaning depend
   only on `propext`, `Classical.choice`, `Quot.sound`; no axiom is declared in a protected module.
4. Comparator's own test suite passes on the pinned toolchain (14 tests). The lower baseline
   verifies end to end: statement match, axiom closure, kernel replay accepted.

## Correspondence with the paper

| Paper (Section 2) | Lean | Note |
|---|---|---|
| Random oracle, 256-bit answers, keyed by label and bit string | `hashSpec`, `Query := Label × Σ k, BitVec k`, `randomOracle` | inputs of different lengths are different queries |
| Cost ⌈|u|/512⌉, label free | `blockCost`, `queryCost`; uniform sampling costs 0 | F2 |
| Sources, deterministic nodes, hash nodes; one parent per hash node; distinct labels | `NodeKind`, `Graph.label_injective` | F1 |
| Root is a hash node | `Graph.root_isHash` | |
| Key generation evaluates all nodes; cost Σ c_g ≤ 1024 | `Graph.keygen`, `keygenCost`, `Scheme.keygen_le` | |
| Disclosure sets exclude the root and meet every source-to-root path | `root_not_mem`, `no_hidden_source` | |
| Reconstruction stops at revealed nodes; E_i = hash nodes evaluated | `Graph.Visited`, `evaluated`, `reconstruct` | root always evaluated |
| C_i = 1 + Σ_{g∈E_i} c_g | `Scheme.verifyCost` | |
| idx(m, η) = first 128 bits of H(enc, m‖η) | `index`, `setWidth idxBits` | F3 |
| Signing: fresh random nonces, at most L trials | `Scheme.sign`, `signLoop`, `trialLimit` | |
| Verification: recompute idx, check length, reconstruct, compare 128-bit prefix | `Scheme.verify`, `publicKey` | |
| Forgery: accepted pair ≠ the signer's pair; any accepted pair if signing failed | `experiment` | strong unforgeability, as in the paper |
| Security: cost ≤ B on every execution ⇒ Pr[Forge] < B/2^127 | `CostAtMost`, `Scheme.Secure` | F5 |
| Parameters table | `paperParams` | all eleven values match |
| Theorem: max_i C_i ≥ 25 | `VerificationLowerBound paperParams 25` | proved by the lower baseline |

## Findings

- **F1 (info).** The graph need not have a unique sink, and a node need not reach the root. The
  paper requires both. Harmless: verification only touches nodes reached from the root, and extra
  nodes only consume key-generation and signature budget. Kept.
- **F2 (info).** A hash node's parent may have output length 0; the paper requires a positive
  length. Such a node costs one compression and is publicly computable, so it changes neither security
  nor cost. Kept.
- **F3 (info).** The index is the low 128 bits of the hash (`setWidth`); the paper says "the first
  128 bits". Any fixed 128 bits are equivalent. Kept.
- **F4 (info).** `sampleAssignment` samples a value for every node; only the sources' values are
  used. Sampling is free. Kept.
- **F5 (info).** `Secure` quantifies over every budget `B` for which `CostAtMost` holds. The bound
  `B/2^127` is monotone in `B`, so this is the paper's requirement stated for all valid budgets.
  Kept.
- **F6 (info).** Adversary computation is unbounded and its private randomness is free; only
  oracle queries are charged. This is the paper's model. The adversary's state type lives in
  `Type`, which restricts nothing in practice. Kept.
- **F7 (open until freeze).** `VerificationLowerBound paperParams c` is vacuous if no scheme
  satisfies `Secure`. Non-vacuity is established by a kernel-checked upper-bound baseline. The
  contract is not frozen before the paper's 106-compression scheme verifies on the upper track.

## Freeze procedure

1. Resolve F7 (upper baseline verified).
2. Set `contract.version` in `challenges.json` to `ots-v1`, run `verifier/pin_contract.py pin`,
   and record the contract id printed there on the site.
3. From then on, any change to a protected file is `ots-v2`: the v1 leaderboard is archived and
   both tracks re-baseline.
