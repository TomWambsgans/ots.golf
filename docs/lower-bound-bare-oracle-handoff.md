# Handoff: the verification lower bound in the bare-oracle model

You are continuing a task in the repository `/Users/e/Documents/zk/sig.golf` (Lean 4 v4.33.1, Mathlib,
VCVio; Python service; LaTeX paper). Work on git branch **`bare-oracle`** only. Do not touch `main`.
Do not push, do not deploy, do not run anything against the production server: the user works on
localhost and pushes when they decide. Commit locally on the branch at milestones, with the trailer
`Co-Authored-By: Claude Fable 5.1 <noreply@anthropic.com>`.

## 1. What the project is

ots.golf is a two-track, Lean-kernel-verified competition on the worst-case verification cost, in
"compressions", of hash-based one-time signatures. The contract is `formal/OptimalOTS/Statement.lean`
(protected, pinned in `verifier/protected.sha256`). The upper track submits a scheme with proofs of
security and cost; the lower track proves `VerificationLowerBound paperParams c` (every weakly secure
scheme has a signature costing at least `c`). Read, in this order: `AGENTS.md`, `docs/AUDIT.md`,
`docs/lower-bound-proof.md`, `docs/bare-oracle-port.md` (working notes of the current branch, keep
it updated), `formal/OptimalOTS/Statement.lean`, `formal/OptimalOTS/Weak.lean`.

## 2. The model change that this branch implements

The user decided that the contract must expose ONE random oracle on bit strings and nothing else: no
labels, no tweaks, no domain separation of any kind, neither between hash nodes nor between hash nodes
and the index query. On `main` the contract has `Label` (`enc` | `node τ`), every hash node carries a
label, `Graph.label_injective` forces distinct labels, and the index query uses `enc`. On the branch
(already done, builds, re-pinned, contract id `b1abfba0…`):

```lean
abbrev Query := Σ k : ℕ, BitVec k                    -- a query is a string with its length
def hash (P) {k} (u : BitVec k) : OracleComp (Spec P) (BitVec P.hashBits)
NodeKind.hash (parent) (parent_lt) (len_eq)          -- three fields, no label
-- no NodeKind.label?, no Graph.label_injective
evalNode … | .hash p _ h => (fun y => y.cast h.symm) <$> hash P (x p)
index P m η = (fun y => (y.setWidth P.idxBits).toNat) <$> hash P (m ++ η)
queryCost … | .inr q => blockCost P q.1              -- ⌈k / 512⌉, at least 1; nothing else charged
```

Everything else (graphs of sources / arbitrary deterministic nodes / hash nodes, `2^115` disclosure
sets that are cuts, signing with up to `2^20` fresh uniform nonces, `experiment` / `Scheme.Secure`
(strong unforgeability), `weakExperiment` / `Scheme.WeaklySecure` (forgery on a new message only),
`VerificationLowerBound P c := ∀ S, S.WeaklySecure → ∃ i, c ≤ S.verifyCost i`, `paperParams`) is
unchanged. `verifyCost i = idxCost P + reconstructCost (sets i)` with `idxCost paperParams = 1`.

**Status on the branch.** The upper-track baseline (`formal/Submissions/Upper/`, the forest of 63
chains under 21 and 7 digests, claim 106) is fully ported and accepted by the official verifier: the
scheme prepends a 16-bit tweak to every hash input (node `ci k t`, tweaked `gc`/`ec`/`rc`, 2795 nodes),
and the proof reads from the string what a label used to say (`Graph.Tagging` in `Keygen.lean`,
`tagNat`/`tagging` in `Names.lean`/`Values.lean`, the event `Spr` restricted to tweaked strings). See
`docs/bare-oracle-port.md` for the whole port. **The lower-track baseline (`formal/Submissions/Lower/`,
claim 25) has NOT been ported: it still uses labels and does not build against the new contract. That
is your job.**

## 3. Your goal

Prove, in Lean, without `sorry`, without `native_decide`, with only `propext`/`Quot.sound`/
`Classical.choice`, a theorem `OptimalOTS.Challenge.Lower.candidate : VerificationLowerBound paperParams c`
for the LARGEST `c` you can rigorously establish **for all schemes of the bare model**, with no side
condition of any kind on the scheme (no "separated"/"tagged"/"collision-free" hypothesis: the user
explicitly refused that route). `c = 25` is the labeled-model constant; **`c < 25` is acceptable**, the
user said so. Update `formal/Submissions/Lower/claim.txt`, `challenges.json` (`baseline` of the lower
track; protected, then `python3 verifier/pin_contract.py pin`), the paper (`paper/looking-for-optimal-OTS.tex`,
Sections 3 to 6 and the theorem), `docs/lower-bound-proof.md`, `docs/AUDIT.md`, `AGENTS.md`, `README.md`,
`llms.txt`, the rules page (`service/app/templates/_how.html`) and the tools' defaults so that every
stated number is the proved one. Verify at the end with:

```sh
cd formal && lake build OptimalOTS Submissions
cd .. && python3 verifier/pin_contract.py check
python3 verifier/check_submission.py lower
python3 verifier/verify.py lower --source .          # the official pipeline, ~3 min; must print "verified"
python3 verifier/verify.py upper --source .          # must still verify (claim 106); do not edit Submissions/Upper
```

Recommended engineering order, so the branch is never left without a certificate:
1. First restore a small but VERIFIED lower certificate against the bare contract (a few hours):
   the elementary bound. Every signature pays the index query (`idxCost = 1`) and the root (a hash
   node, never in a set, always evaluated, `blockCost ≥ 1`), so `c = 2` needs about thirty lines.
   With more work `c = 3` follows from an elementary attack (a scheme whose verifier evaluates only
   the root is forgeable by brute-force search of a preimage of the root input plus a nonce search).
   Commit that as the interim baseline (claim.txt, challenges.json, pin).
2. Then build the real theorem (Sections 4 and 5 below) and raise the claim.

## 4. The mathematics: what is known, what is open

The paper's proof (Sections 3 to 6) uses distinct labels essentially. §3.1: "Each hash node uses a
distinct oracle label... Consequently Z, Y_1, ..., Y_n are mutually independent and uniform"; the
posterior on candidates is uniform; in the construction bound (Lemma 3) the oracle entries at the
labels of `J` other than the `m` pinned ones are independent and uniform. In the bare model:

(a) Records are not uniform: `I_g = I_g'` (equal input strings of two hash nodes) forces `Y_g = Y_g'`.
(b) Hence the posterior given the observations is not uniform on the candidate set.
(c) The oracle restricted to the strings an attempt may query is pinned, given the record, at every
    keygen point in that domain, not only at the `m` points of `J`.
(d) Index queries `H(m ‖ η)` can coincide with node queries; the Lean attacker's fixed messages
    `msg₁ = 0`, `msg₂ = 1` provably fail (a scheme can plant a constant-input hash node on `0 ‖ 0`).

A research pass (read-only, by a subagent of the previous session) produced the following, which you
must re-derive and check yourself before relying on it; treat it as a plan, not as established:

* **(d) is solved.** Introduce a separated experiment `Exp'` where the index uses an independent
  oracle `H_enc`; every independence claim of §6 (`Product.lean`, `Sign.lean`, `Nonce.lean`) holds in
  `Exp'` verbatim. Couple `Exp'` with the bare `Exp` (same `H` on node strings); they are identical
  until some string is queried in both a node role and an index role (`Bad`), so
  `Pr_bare[Forge] ≥ Pr_Exp'[Forge] − Pr[Bad]`. With the attacker's two messages drawn UNIFORMLY AT
  RANDOM (and distinct), averaging over the messages gives `Pr[Bad] ≤ 2 · (number of 512-bit
  node-role queries ≈ 2^119.8) / 2^256 ≈ 2^-135`. The attacker must therefore change: random
  messages instead of `msg₁ := 0`, `msg₂ := 1` (`Attack.lean`); `nonceEmb_injective` only needs
  `m₁ ≠ m₂`.
* **Fresh values.** Process hash nodes in order; sample `(Z, Ŷ_1..Ŷ_n)` uniform on the product; let
  `first(g)` be the least `h ≤ g` with the same input string; `Y_g := Ŷ_first(g)`. This map `Φ` is
  deterministic and `Φ(uniform)` is the true bare record law. Candidates `Ĉ = obs⁻¹(x, y)` in fresh
  space; `Q := Unif(Ĉ)` IS the correct posterior (solves (a), (b)). Weights
  `ĥ(g) = 256 − Ent_Q(Ŷ_g | Z, Ŷ_<g)`, `h_i(g) = ĥ(g)` for `g ∉ E_i`, `0` on `E_i`; a repeated
  (duplicate-input) node has weight 0.
* **Construction bound (Lemma 3).** With the attempt sampling from the working set according to `Q`
  (the attacker is computationally unbounded), the KL argument of §4 transfers; the oracle-entropy
  step becomes `Ent(O | T) = 256 (N_J − #distinct J-inputs) ≥ 256 (N_J − m)`, which only helps.
  ONE STEP IS OPEN and the previous session found a counterexample to it as stated: the claim "given
  only the trace, all other entries of `O` are independent and uniform" fails when a hidden node
  (neither revealed nor reconstructed) has an input string inside the attempt's query domain and its
  output feeds a checked node (e.g. a hidden node with a public constant input whose output determines
  a `J`-node's input): then `Ent(T | O) ≥ Ent(T) − 256 m` is false, although the final conclusion
  `E[−log p] ≤ d` still holds in that example. Either restrict `O` more cleverly, or prove the
  conclusion by a different route (e.g. compare the attempt with sampling the true posterior directly
  and bound `E[−log p]` through the chain rule over the queried strings, treating an entry pinned by a
  hidden node as part of the record), or change the attempt (e.g. it may also query the strings of
  such confusable nodes if that keeps the cost budget). This is the first thing to settle on paper.
* **Information bound (Lemma 2) is the crux.** In fresh space the exact identity
  `Σ_{g ∉ E_i} ĥ(g) ≤ −log Pr[obs] − 256 |F_i|` holds, where `F_i` = first-occurrences among `E_i`.
  When two RECOMPUTED nodes can share an input string (`|F_i| < |E_i|`), the naive count of
  observations over-charges. Rigorous but lossy fix: partition by the input-collision pattern on
  `E_i`; `Pr[Σ_{g∉E_i} ĥ(g) > ℓ_i + u] ≤ Bell(|E_i|) · 2^{-u}`. With `|E_i| ≤ 23`, `Bell(23) ≈ 2^55`, so
  the budget `S_*` inflates from 5257 to about 5309. Structural (probability-1) collisions cost
  nothing; the Bell factor is the worst case over adversarial probabilistic collisions (a 1-bit source
  feeding two hash nodes). A tight (Bell-free) bound was NOT found: the abstract lemma
  `card_infoWeight_gt_le` (`Information.lean`) gives `2^{-u}` with weights computed on a slightly
  different candidate set, and the two weight sums differ by up to 256 per "reconstructed node whose
  input first appears at a hidden node". If you can bound the number of reconstruction collisions by
  a small constant using the cut/DAG structure, or prove the equality of the two weights in general,
  25 may be recoverable.
* **Counting bound (§5), Appendix A, `Counting.lean`, `CountingFactor.lean`, `Repetition.lean`,
  `Entropy*.lean`: unchanged.** They only use nonnegative weights vanishing on `V_i`, `|V_j| ≤ a`, and
  a total-weight budget.
* **Numerics (§6, Appendix B).** The only changed constant is `S_*`. The pivotal quantity
  `2^115 · β_22(123)` is 103.65 at `S_* = 5257` (must exceed 100), 99.93 at 5266, 83.96 at 5309: the
  paper's `a = 22` attack (constant 25) tolerates only about +8 bits, so with the Bell inflation
  **25 fails numerically**. With `a = 21` (assume `C_i ≤ 23 ⇒ |V_i| ≤ 21`, i.e. constant 24):
  `2^115 · β_21(123) ≈ 2530` at `S_* = 5309`, a 25× margin. The full success-vs-cost optimisation at
  `a = 21` was NOT re-run; do it with `tools/tune_lower_bound.py` (read its docstring; it models the
  operating point of the attack: `a`, `v`, `K`, `q`, `T`, `d0`; `--idx 1`). The current Lean numerics
  (`NumericsDefs.lean`, `Numerics*.lean`, `TailBound.lean`, `RankIntegral.lean`, `AvgSucc.lean`,
  `Ranks.lean`, `Assembly.lean`) are for `a = 22, K = 100, q = 5·2^113, T = 3·2^121, d0 = 123,
  threshold 11/200`; `git show 0674da6:formal/Submissions/Lower/` and neighbouring commits on `main`
  contain an earlier variant with a K/K′ split and a certificate generator
  (`tools/gen_lower_numerics.py` at commit `33e2a23^`) that may be adaptable.
* **Expected outcome:** 24 unconditionally, if the two open steps close (construction-bound
  oracle-independence; numerics at `a = 21`). 25 is open. If 24 also fails, go down until it holds;
  every lower `c` uses the same machinery with more slack.

## 5. The Lean development to port (`formal/Submissions/Lower/`, ~6400 lines)

Read `docs/lower-bound-proof.md` for the file map. Where labels are used, precisely (the previous
session traced this):

* `AnalysisDefs.lean`: `Cell S := (Σ v, BitVec (inLen v)) ⊕ EncIn P` (one cell per hash node input, one
  per index-query input) and `decode : Query → Option (Cell S)` pattern-match on `.enc` / `.node τ`
  and use `label?`. In the bare model a cell is a bare string; node cells collide with each other and
  with index cells. This is where `Exp'` and the fresh-value space enter: define the analysis in
  `Exp'` (independent `H_enc`, so index cells stay separate) and use cells = strings for the graph.
* `Cells.lean`: `decode_injective`, "every hash query of the attack decodes".
* `LazyEagerDefs.lean`, `LazyEager.lean`: the lazy random oracle equals a uniform table on the queried
  cells (generic; should survive with string cells).
* `Product.lean`: splitting a uniform table into the graph part and the nonce parts (`nonceEmb`,
  needs only `m₁ ≠ m₂` once index cells are separate).
* `Decomp.lean`: the experiment with a fixed table is at least an explicit sum; uses
  `S.graph.label_injective` once (line ≈ 68) to decode a query to its node.
* `Sign.lean`, `Nonce.lean`: signing index and nonce search with a nonce table; unchanged in `Exp'`.
* `Information.lean`: `card_infoWeight_gt_le` needs the record uniform on the product space; reuse it in
  fresh space, or add the Bell-partition lemma.
* `ConstructionDefs.lean`, `Construction.lean`: `card_tables_consistent` assumes one independent table
  per node; the abstract lemma `sum_neg_logb_attemptProb_le` is stated over abstract `Rec, C, I, Y` and
  is reusable in fresh space with the distinct-string count added.
* `Attack.lean`: `msg₁ := 0`, `msg₂ := 1` must become random distinct messages (or scheme-dependent
  ones chosen by an averaging argument, via `Classical.choose`); the two stages are `choose` (may
  randomise) and `forge`.
* `Cost.lean`: already generic in `idxCost`; unchanged otherwise.
* `Assembly.lean`, `Solution.lean`: thread the `2^-135` term and the new constant.
* A new file for the identical-until-bad coupling between `Exp` and `Exp'`: the upper proof's
  `Submissions/Upper/IUB.lean` and `Master.lean` contain a general identical-until-bad framework over
  caches (`Cache.Hits`, `Cache.extend`, `Cache.Disjoint`) that you may copy (submissions may only
  import `OptimalOTS.Statement`, Mathlib, VCVio and siblings of their own root; copy, do not import
  across tracks).

Pitfalls of this code base (empirical, cost a lot of time before they were understood):
never let the elaborator unfold `Finset.univ` over huge types (records, `Fin 63 → Fin 15`, node
types), `experiment`, `weakExperiment`, a `2^20`-iteration loop, `Graph.encode`: "maximum recursion
depth". Keep such definitions behind `irreducible_def` / `@[irreducible]` /
`attribute [local irreducible] …`; use `set_option linter.constructorNameAsVariable false` where
needed; prefer `rw` / `simp only [Finset.mem_filter, Finset.mem_univ, true_and]` / `unfold` over
`exact` / `congr 1` / `rfl` on such goals; in this Mathlib `∈` on `Finset` is `SetLike.instMembership`
and `mul_le_mul_right (h : b ≤ c) a : a * b ≤ a * c`, `add_le_add_right (h : b ≤ c) a : a + b ≤ a + c`.
`16 + 128` unifies with `144` by literal arithmetic; pass widths explicitly when `?n` unification
stalls. A stale shape can surface as a `whnf` timeout rather than a type error.

Build one module at a time: `cd formal && lake build Submissions.Lower.<File>`. Never run `lake clean`
or `lake update`; never touch `.lake`. Subagents working on disjoint files in parallel worked well for
the upper port (four at a time; Lake serialises builds); give each a precise brief with the interface
decisions, and keep `docs/bare-oracle-port.md` as the shared record of decided interfaces.

## 6. Reporting

When you stop (done, or blocked), report: the constant proved and verified (`verify.py lower` output);
exactly which mathematical steps you proved and how (paper section references); what remains open;
the list of files changed; and any statement you had to weaken, with the reason. Do not claim a bound
that the verifier did not accept. The user reads plain, factual reports; lead with the outcome.
