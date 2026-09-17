# Porting both proofs to the bare oracle (working notes, branch `bare-oracle`)

Temporary file: delete before merging.

## What changed in the contract (`formal/OptimalOTS/Statement.lean`, already done, builds)

There is ONE random oracle and no labels:

```lean
abbrev Query := Σ k : ℕ, BitVec k                       -- was: Label × (Σ k, BitVec k); `Label` is gone
def queryCost P | .inl _ => 0 | .inr q => blockCost P q.1     -- was q.2.1
def hash (P) {k} (u : BitVec k) : OracleComp (Spec P) (BitVec P.hashBits)   -- no label argument
NodeKind.hash (parent) (parent_lt) (len_eq)             -- THREE fields; the `label : ℕ` field is gone
-- `NodeKind.label?` and `Graph.label_injective` are gone
evalNode … | .hash p _ h => (fun y => y.cast h.symm) <$> hash P (x p)
index P m η = (fun y => (y.setWidth P.idxBits).toNat) <$> hash P (m ++ η)   -- was hash P .enc (m ++ η)
```

So a query is just a bit string with its length. Distinct hash nodes are no longer separated by the
model, and the index query is no longer separated from node queries. A scheme separates them itself,
inside the strings it hashes.

## How the proof replaces labels

* **Index queries are the queries of length `P.msgBits + P.nonceBits`** (512 for `paperParams`):
  `encQuery u := ⟨P.msgBits + P.nonceBits, u⟩`. Every statement that said "`f (.enc, ⟨k, u⟩) = none`
  for all `k u`" now says "`f (encQuery u) = none` for all `u : EncInput P`", i.e. the cache has no entry
  of index-query length. Node queries of the scheme never have that length.
* **Node queries are recognised by a public tag function.** A label used to say which hash node a
  query belongs to; now a function on strings does:

  ```lean
  /-- A public way to read, from a query, the hash node it belongs to. -/
  structure Graph.Tagging (G : Graph P) where
    tag : Query → Option (Fin G.size)
    /-- The parent of every hash node is a deterministic node whose output always carries the tag
    of that hash node. -/
    tag_parent : ∀ v p hp hl, G.kind v = .hash p hp hl →
      ∃ ps hps f hf, G.kind p = .det ps hps f hf ∧ ∀ x, tag ⟨G.len p, f x⟩ = some v
  ```

  It is defined in `Keygen.lean`. With it, "points of different hash nodes differ" holds for every
  assignment whose deterministic nodes are consistent (in particular `G.evalRec ξ`, and the partial
  assignments of the evaluation fold once the parent has been evaluated).
* **The concrete scheme puts a tweak in every hash input.** Tweak width `W = 16` bits,
  `tw h : BitVec 16 := BitVec.ofNat 16 h.idx` for a hash node named `h`. New node kind in `Names.lean`:

  | name | meaning | length | kind |
  |---|---|---|---|
  | `ci k t` | `tw (ch k t) ++ (value of prev k t)`, the input of the chain hash `ch k t` | 144 | det, parent `prev k t` |
  | `ch k t` | `H(ci k t)` | 256 | hash, parent `ci k t` (was `prev k t`) |
  | `gc j` | `tw (gh j) ++ c ‖ c ‖ c` | 400 (was 384) | det |
  | `ec l` | `tw (eh l) ++ g ‖ g ‖ g` | 400 (was 384) | det |
  | `rc` | `tw rh ++ e_0 ‖ ⋯ ‖ e_6` | 912 (was 896) | det |

  Revealed nodes are unchanged (`src`, `cv`, `gv`, `ev`: 128 bits each), so signatures are unchanged.
  Costs are unchanged: 144 and 400 bits cost one compression, 912 bits cost two, none has length 512.
  New topological index (parents first): `src k ↦ k`, `ci k t ↦ 63 + 189 t + k`,
  `ch k t ↦ 126 + 189 t + k`, `cv k t ↦ 189 + 189 t + k`, `gc j ↦ 2709 + j`, `gh j ↦ 2730 + j`,
  `gv j ↦ 2751 + j`, `ec l ↦ 2772 + l`, `eh l ↦ 2779 + l`, `ev l ↦ 2786 + l`, `rc ↦ 2793`,
  `rh ↦ 2794`, `N = 2795`.

## Rules for everyone working on this

* Build one module with `cd formal && lake build Submissions.Upper.<File>`. Concurrent builds wait on
  Lake's lock; that is fine. NEVER run `lake clean`, `lake update` or touch `.lake`.
* Edit ONLY the files you were given. Other people are editing the other files at the same time.
* No `sorry`, no new axioms, no `native_decide`. Keep theorem names and statement shapes; when a
  statement must change, change it minimally and REPORT the exact new signature.
* Known pitfalls of this code base: never let the elaborator unfold `Finset.univ` over `Name`,
  `Fin 63 → Fin 15`, records, `graph`, `experiment`, `forestScheme`, `family`, `shapes`
  ("maximum recursion depth"); keep such things behind `irreducible_def` / `@[irreducible]` /
  `attribute [local irreducible]`; prefer `rw` / `simp only [...]` / `unfold` over `exact` / `congr 1` /
  `rfl` on goals mentioning them; `set_option linter.constructorNameAsVariable false` where needed.
  In this Mathlib `mul_le_mul_right (h : b ≤ c) a : a * b ≤ a * c` and
  `add_le_add_right (h : b ≤ c) a : a + b ≤ a + c`.

## Done (building)

* `Reconstruct.lean`: `hash_support` lost its label argument (`hash_support u c`); the hash clause of
  `ReconEqAt`/`ReconEqs` binds `p hp hl` (no τ) and speaks of `d ⟨G.len p, y p⟩`; `index_support` and
  `verify_support` speak of `p.2 ⟨P.msgBits + P.nonceBits, m ++ η⟩` (defeq to `encQuery P (m ++ η)`).
* `SignIdx.lean`: `encQuery P u := ⟨P.msgBits + P.nonceBits, u⟩`; `run_signIdx_extend` /
  `run_signIdxLoop_extend` take `hf : ∀ u : EncInput P, f (encQuery P u) = none`;
  `EncInvariant Φ := ∀ c (u : EncInput P) w, Φ (c.cacheQuery (encQuery P u) w) = Φ c` (no `k`);
  new lemmas `encQuery_fst`, `ne_encQuery_of_length_ne (hq : q.1 ≠ msgBits + nonceBits) u : q ≠ encQuery P u`,
  `exists_eq_encQuery_of_length_eq (hq : q.1 = …) : ∃ u, q = encQuery P u`. `EncCharges.lean` unchanged.
* Downstream hints: `Potentials.lean:388-394` (`node_ne_encQuery`, `enc_ne_encQuery`) become a split on
  `k = msgBits + nonceBits`; `StageB.lean:83,116` need a length argument; `Values.lean` lemmas `kc_enc`,
  `fExp`/`fHid` at enc points and the `Spr` enc lemma are restated for `encQuery paperParams u`.
* `Keygen.lean`: `Graph.Tagging` (fields `tag`, `tag_parent`), `TagOK T x`, `tagOK_evalRec T ξ`,
  `point_evalRec_inj T ξ ξ'`, `point_inj T hx hx'`; `G.point x v = some ⟨G.len p, x p⟩`;
  `point_eq_some_iff : … ↔ ∃ p hp hl, G.kind v = .hash p hp hl ∧ q = ⟨G.len p, x p⟩`;
  `point_eq_none_of_not_isHash`; `keygenCache_apply_iff T ξ q w`, `keygenCache_isSome_iff T ξ q`;
  `E_run_evaluate T z g`, `E_run_keygen S T g` (same right-hand sides). Cost lemmas unchanged.
  Call sites to adapt: `Values.lean:247` (`Graph.keygenCache_apply_iff graph T ξ q w`),
  `Assembly.lean:230` (`E_run_keygen forestScheme T g'`). The concrete `T : graph.Tagging` must cover
  every hash node, the root included.
* `Names.lean` / `Tree.lean` / `Cuts.lean` (Scheme.lean unchanged, claim 106): constructor order is now
  `src, ci, ch, cv, gc, gh, gv, ec, eh, ev, rc, rh`; `N = 2795`; lengths `ci ↦ 144`, `gc, ec ↦ 400`,
  `rc ↦ 912`; `child (src k) = ci k 0`, `child (ci k t) = ch k t`, `child (cv k t) = ci k (t+1)` for
  `t < 13` (`child_cv_of_lt`); `parents (ch k t) = {ci k t}`, `parents (ci k t) = {prev k t}`;
  `Name.sum_eq` has a `ci` term after `src`. Tweaks (HIGH bits, `tw h ++ payload`):
  `tw`, `tw_toNat`, `tw_injective`, `append_inj`, `tw_append_inj`, `tw_append_eq_iff`, `tw_query_inj`,
  `tagNat (q : Query) : ℕ := q.2.toNat / 2 ^ (q.1 - 16)`, `tagNat_append`, `tagNat_tw_append`,
  `tagNat_cast`, `detVal_ci/gc/ec/rc` (rfl lemmas, e.g.
  `detVal (.ci k t) x = tw (ch k t) ++ trunc (x (prev k t).fin)`),
  `tagNat_detVal (hc : child p = some h) (hh : h.cost ≠ 0) x : tagNat ⟨p.len, detVal p x⟩ = h.idx`,
  `tagNat_cast_detVal`. Low bits are untouched, so `trunc (tw h ++ cat3 x y z) = z` still holds.
  `IsCut.values` (every cut node has length 128) means `ci`, `gc`, `ec`, `rc` are never in a cut.
  Cuts.lean: new `ci_not_mem_cutOf`, `evaluated_ci_iff'`, `evaluated_ci_iff`.

## Design of the convergent files (decided)

* `hashParent (ch k t) = some (ci k t)` (was `prev k t`); `gh ↦ gc`, `eh ↦ ec`, `rh ↦ rc` unchanged.
* `pointOf ξ h p : Query := ⟨p.len, val ξ p⟩` (no label). Its tag: `tagNat (pointOf ξ h p) = h.idx` when
  `hashParent h = some p`. `pointOf_inj_left` therefore needs both `hashParent` hypotheses. Its length is
  144, 400 or 912, never `paperParams.msgBits + paperParams.nonceBits = 512`.
* The concrete tagging: `def tagging : graph.Tagging` with
  `tag q := if h : tagNat q < N then some ⟨tagNat q, h⟩ else none`.
* The event `Spr` is restricted to strings carrying the node's tweak, otherwise one fresh answer could be
  a spurious preimage for every node with that input length (the multi-target loss tweaks exist to avoid):
  ```lean
  def Spr (c : Cache paperParams) (ξ : Rec) : Prop :=
    ∃ h p, hashParent h = some p ∧ ∃ u : BitVec p.len, u ≠ val ξ p ∧ tagNat ⟨p.len, u⟩ = h.idx ∧
      ∃ w, c ⟨p.len, u⟩ = some w ∧ trunc w = trunc (ξ.2 h.fin)
  ```
  A fresh query `q` can create a `Spr` entry for at most one `h` (the one with `h.idx = tagNat q`), so
  `spr_charge` keeps its bound `ε`. In `Events.lean` the witness `u = yv y p` satisfies the tag condition
  because the parent `p` of an evaluated hash node is itself evaluated (it cannot be in a cut, its length
  is not 128), hence `yv y p = detVal p y` (`yv_det`) and `tagNat_detVal` applies.
* Lemmas about enc-labelled points (`kc_enc`, `fExp_enc`, `fHid_enc`, `spr_cacheQuery_enc`) are restated for
  `encQuery paperParams u` with `u : EncInput paperParams`.

## `Values.lean` (done, building; it now also imports `SignIdx`)

Changed statements (names kept):
```lean
theorem val_gc ξ j : val ξ (gc j) = tw (gh j) ++ cat3 (trunc (ξ.2 (ch (chainOf j 0) 13).fin)) (…1…) (…2…)
theorem val_ec ξ l : val ξ (ec l) = tw (eh l) ++ cat3 (trunc (ξ.2 (gh (groupOf l 0)).fin)) (…) (…)
theorem val_rc ξ : val ξ rc = tw rh ++ cat7 fun l => trunc (ξ.2 (eh l).fin)
def hashParent   -- ch k t ↦ some (ci k t); gh ↦ gc; eh ↦ ec; rh ↦ rc
def pointOf (ξ : Rec) (_h p : Name) : Query := ⟨p.len, val ξ p⟩
theorem pointOf_inj_left (hp : hashParent h = some p) (hp' : hashParent h' = some p')
    (e : pointOf ξ h p = pointOf ξ' h' p') : h = h'
theorem kc_enc (ξ) (u : EncInput paperParams) : kc ξ (encQuery paperParams u) = none
theorem fExp_enc (A?) (ξ) (u : EncInput paperParams) : fExp A? ξ (encQuery paperParams u) = none
theorem fHid_enc (A?) (ξ) (u : EncInput paperParams) : fHid A? ξ (encQuery paperParams u) = none
def Spr c ξ := ∃ h p, hashParent h = some p ∧ ∃ u : BitVec p.len, u ≠ val ξ p ∧ tagNat ⟨p.len, u⟩ = h.idx ∧
    ∃ w, c ⟨p.len, u⟩ = some w ∧ trunc w = trunc (ξ.2 h.fin)
  -- destructuring pattern is now ⟨h, p, hp, u, hu, htag, w, hw, ht⟩ (one more component)
theorem spr_cacheQuery_enc c ξ (u : EncInput paperParams) w : Spr (c.cacheQuery (encQuery paperParams u) w) ξ ↔ Spr c ξ
def deps  -- new case: | ci k t => if h : t.val = 0 then {src k} else {ch k ⟨t.val - 1, _⟩}
```
Added: `trunc_eq_self`, `trunc_injective_of_len (hw : w = 128)`, `val_ci`, `val_ci_zero`, `val_ci_succ`,
`cost_ne_zero_of_hashParent`, `hashParent_inj`, `len_hashParent_cases` (144 ∨ 400 ∨ 912),
`len_hashParent_ne_enc`, `pointOf_fst`, `tagNat_val`, `tagNat_pointOf`, `pointOf_ne_encQuery`,
`mk_ne_encQuery (hp) (u' : BitVec p.len) u : (⟨p.len, u'⟩ : Query) ≠ encQuery paperParams u`,
`tagOf`, `tagOf_eq_some_of_tagNat`, `graph_kind_hashParent`, `graph_kind_eq_hash`,
`val_eq_detVal (hp) ξ : val ξ p = detVal p (graph.evalRec ξ)`,
`tagNat_detVal_of_hashParent (hp) (x : Asg) : tagNat ⟨p.len, detVal p x⟩ = h.idx`,
`def tagging : graph.Tagging`, `tagging_tag`, `tagging_tag_pointOf`, `deps_ci`, `deps_ci_zero`,
`deps_ci_succ`, `child_src_ci`, `child_cv_ci`, `val_updSrc_src_of_ne`, `trunc_tw_append`,
`trunc_of_tw_append_eq`, `trunc_of_tw_eq`, `trunc_of_tw_cat3_eq`, `trunc_of_tw_cat7_eq`.

Known downstream breakages reported by the Values port:
* `Resample.lean` ≈247 `mem_deps_cases'` is FALSE for `n = ci k 0` (`deps = {src k}`, and `src k` is neither
  `n` nor a `hashOf` target): it needs a fourth alternative such as `child s = some n`; in
  `not_mem_deps_of_hiddenCoord` that case closes with `evaluated_of_child_res` when `n` is evaluated and with
  `n.len = 144 ≠ 128` when `n ∈ A`. `Resample.lean:484,517`: `pointOf_inj_left hp hp' e`.
* `Events.lean:114-125`: `val_gc'`/`val_ec'`/`val_rc'` need the `tw _ ++` prefix; peel a chain input with
  `tw_append_inj`/`append_inj` then `trunc_injective_of_len (Name.len_prev k t)`; `Events.lean:139`: three-field
  `.hash`; `Events.lean:319`: `child (cv k t) = some (ci k ⟨t+1,_⟩)`; chains now alternate `ci → ch → cv`.
* `Assembly.lean:96` `(fun u => kc_enc ξ u)`; `:127` and `Potentials.lean:270` `spr_cacheQuery_enc c ξ u w'`;
  `Assembly.lean:230` `E_run_keygen forestScheme tagging g'`; `Potentials.lean:409,476` `fun ξ => kc_enc ξ u₀`,
  `:445` `fun ξ => fHid_enc (some Ac) ξ u₀`; `StageB.lean:83` `rw [hqe, kc_enc]` (do not unfold `encQuery`),
  `:135,147` `fun u => fExp_enc A? ξ u`.
* Tactic pitfalls: `NodeKind.hash.injEq` does not fire in `simp only` on `graph.kind h.fin = .hash q hq hl`
  (use `NodeKind.hash.inj hk`); `rw [trunc_trunc]` fails on widths only defeq to 128 (use `congrArg`); a stale
  pre-tweak `cat3`/`cat7` shape against a `tw _ ++ cat3 …` goal shows up as a `whnf` TIMEOUT, not a type error;
  pass `(n := 128)` etc. explicitly to `tagNat_tw_append`, `append_inj`, `trunc_of_tw_append_eq`.

## `Resample.lean` and `Events.lean` (done, building)

* `Resample.lean`: every statement used downstream is unchanged (`hits_charge_A`, `hits_charge_B`, `fiberA`,
  `fiberB`, `Data`, `dataOf`, …). Only `mem_deps_cases'` (internal) gained a fourth disjunct.
* `Events.lean`: RENAMED its general lemma to
  `bv_append_inj {n m} {x x' : BitVec n} {y y' : BitVec m} (h : x ++ y = x' ++ y') : x = x' ∧ y = y'`
  (the name `append_inj` now belongs to the 16-bit tweak lemma of Names.lean). `StageB.lean:203` must use
  `bv_append_inj hu` (there `m₂ ++ σ₂.1 = m₁ ++ η` joins two 256-bit halves).
  Unchanged statements: `yv`, `yv_mem`, `yv_det`, `yv_cv`, `yv_gv`, `yv_ev`, `yv_of_hashOf`, `hash_step`, `up`,
  `events_none`, `events_ne`, `events_same` (conclusions `Spr d ξ ∨ Cache.Hits d (kc ξ)`,
  `Spr d ξ ∨ Cache.Hits d (fHid (some A) ξ)`, `Spr d ξ`), `encode_congr`, `trunc_cast_eq`.
  Changed: `graph_kind_hash (hp) : ∃ hlt hl, graph.kind h.fin = .hash p.fin hlt hl`;
  `recon_evaluated` hash clause binds `p hp hl`; `yv_hash … : ∃ w, d ⟨p.len, yv y p⟩ = some w ∧ …`;
  `val_gc'`/`val_ec'`/`val_rc'`/`yv_gc`/`yv_ec`/`yv_rc` carry the `tw _ ++` prefix.
  Added: `cost_hashParent`, `hashParent_ne_src`, `yv_ci`, `yv_ci_ne`, `evaluated_hashParent`,
  `yv_hashParent`, `tagNat_yv`.
  Tactic note: `rw [detVal_gc]` fails on `y : graph.Assignment` (only defeq to `Asg`); use `show … = _`.


## Lower-track work, 2026-09-17

### Verified milestone: unconditional bound 2

`Submissions/Lower/Elementary.lean` proves `Scheme.two_le_verifyCost` for every scheme and every
index, with no security hypothesis: the index costs at least one compression, and the root belongs
to `evaluated`, is a hash node, and costs at least one compression. `Solution.lean` exports
`VerificationLowerBound paperParams 2`. The lower baseline and `claim.txt` are 2; the protected pin
was regenerated (contract id `2e7dff7c4648229c43e9edd5e736d863296f3d32ba4af347e9e7157bc0f30191`).

Official verifier: `verified: track=lower claim=2 commit=worktree in 53.0s`.
The old labeled entropy development remains present for reference while the replacement is explored;
it is not imported by the certificate and has not yet been ported.

### Mathematical obstructions found before porting

The handoff's proposed fresh-coordinate repair is false in both required places, even with
probability-one duplicate inputs. A hidden earlier hash can own the fresh coordinate used by a
later reconstructed hash, putting its entropy deficit outside the reconstruction set. It can also
own the coordinate needed by a newly evaluated node, making the latter's proposed weight zero
while its construction can fail. Detailed independent derivations are being recorded in
`bare-oracle-information-analysis.md` and `bare-oracle-construction-analysis.md`.
Consequently, the Bell-budget numerical calculation alone cannot establish 24.

An alternative under investigation groups indices by their sets of evaluated hash nodes.
When two indices have the same set, the observed oracle input/output pairs permit free conversion
of their disclosures by finite search. If all verification costs are at most 17, the number of
patterns is less than `2^110`; most indices then have several interchangeable targets. This is a
prospective route to 18, not a verified lower bound.

### Parallel file ownership

- Construction: `Semantics.lean`, new `Conversion.lean` / `Encoding.lean`, construction analysis.
- Information: new `Patterns.lean`, information analysis.
- Numerics: `tools/tune_lower_bound.py`, numerics notes, new `CacheFresh.lean`.
- Root: certificate, attack integration, remaining probability/cost modules, project documentation.

No upper-track file is being edited. No push, deployment, or main-branch operation is authorized.

### Second milestone: checked components for the replacement

The two counterexample notes are complete, with exact probabilities. The construction example
has `E[-log2 p] = 1 - 2^-256` but proposed target weight zero. The information example has
outside weight 256 with probability one, zero disclosure, and `Bell(1)=1`.

The following bare-model modules now build independently:
`Semantics`, `Encoding`, `Patterns`, `Cache`, `CacheFresh`, `Expectation`, `Index`, `CostCore`,
and `KeygenSupport`. Records in `Semantics` are only algebraic objects; there is no assertion
that independently uniform node outputs have the bare-oracle law. `KeygenSupport` instead proves
that actual key-generation outputs satisfy their node equations in the final cache.
`Patterns` proves the exact binomial count and that at most one quarter of indices have fewer
than eight matching patterns, assuming all costs at most 17.

`CacheFresh` bounds the number of cached message prefixes by the number of cached strings,
and proves that a cost-bounded run adds at most its cost in cached strings. This permits direct
analysis from a fresh random message after key generation and another after signing; no hypothesis
on scheme labels or tagging is introduced. Signing/search probability and final assembly remain.

The numerical investigation confirms conditional feasibility of 24 at the old simple operating
point, even with budget 5313, but cannot repair the false lemmas. It also corrects the Bell rounding:
`Bell(22)>2^52`, so even the proposed (false) Bell inequality would need budget 5310 rather than 5309.
The tune tool now marks this analysis as conditional and accepts `--s-star`.

### Verified milestone: bare-oracle lower bound 18

The complete pattern attack and assembly now build. `Solution.lean` exports exactly
`VerificationLowerBound paperParams 18`, with only the three allowed axioms. Official pipeline:

```
verified: track=lower claim=18 commit=worktree in 89.5s
```

Log: `/private/var/folders/7g/qxrr2pgj40s3ykbngr10jkkr0000gn/T/ots-verify-9e5s6dgp/verify.log`.
The lower baseline and claim are now 18, protected pin
`9564de9198acd6555659e804186120f228c838c84de0628a608ed4722fa6efce`.

The probability proof uses actual finite caches, not a separated experiment. Messages are sampled
uniformly after key generation and after honest reconstruction. `SignFresh` proves the exact
signing law on a fresh message domain; `PatternSearch` proves its success lower bound `1/9`;
`PatternAttack` proves the conditional forging bound `1/10` and the total cost;
`PatternAssembly` proves success at least `9/200`, above the security threshold.

Unused files of the labeled proof were removed from the submission root so the full library builds.
Their original source is preserved in git at `e2eaf4e`; no historical independent-output law is
part of the replacement. The current file map is in `lower-bound-proof.md`.

The proposed fresh-weight steps were settled by counterexamples, not proved. Bounds 19 through 24
remain open here. The equality-pattern method alone stops at 18, because allowing sixteen nonroot
hash nodes gives more possible patterns than the `2^115` indices. No condition on schemes was added.

### Final verification and report

The final `lake build OptimalOTS Submissions` passed after removal of the obsolete modules.
Contract pin and both submission-policy checks passed. The official pipelines were rerun on the
final submission roots, concurrently:

```
verified: track=lower claim=18 commit=worktree in 117.5s
verified: track=upper claim=106 commit=worktree in 165.6s
```

The paper compiled to nine pages with no warnings or overfull boxes. The tune tool reconfirmed
the exact pattern inequalities at 18 and the failure of this counting estimate at 19; its entropy
mode retains the conditional 24/25 investigation. All project descriptions now state the proved
18/106 bounds. The preceding entries record intermediate states, not outstanding work.

The complete outcome, mathematical limitations, verifier log paths, local milestones, and changed
file list are in [bare-oracle-lower-report.md](bare-oracle-lower-report.md).
`Statement.lean`, `Weak.lean`, and `Submissions/Upper/` are unchanged from the handoff commit.
All work remained local on `bare-oracle`; nothing was pushed or deployed.

## Subsequent work: partial disclosures

After the bare-oracle work was merged locally, a separate restricted framework was added on
`main`: each disclosed payload represents at most 46 hash origins, allowing arbitrary fragments
and deterministic encodings. Its lower bound 80 and upper bound 106 both pass the official
verifier. The unrestricted DAG statement and both original submission roots remain unchanged;
their records are still 18 and 106. The new proof uses ordered pattern counting and an averaged
conversion attack, without oracle separation assumptions. See [partial-disclosures.md](partial-disclosures.md)
for the definition, proof, verification logs and scope of encoded fragments.


## Subsequent work: whole-word restriction

At the user's request, framework 3 now restricts sources to 128 bits and deterministic operations
to concatenation and selecting either fixed 128-bit half of a 256-bit hash output. Inputs may
concatenate any number of whole words. This replaces the 46-origin admission condition;
frameworks 1 and 2 and their proofs remain unchanged.

The syntax implies at most 41 origins in a 5248-bit payload. Ordered counting then gives
choose(131,41) patterns under verification cost at most 92. Sharpening both freshness bounds
from 9/10 to 99/100 gives a success probability strictly above the complete experiment's
127-bit security allowance. The official verifier accepted
`WholeWordVerificationLowerBound paperParams 93` in 134.6 seconds. Exact arithmetic at 93 succeeds and at 94
fails for this estimate. See [whole-words.md](whole-words.md) for the complete argument and
final verification report. The historical partial-disclosure upper proof remains a reference;
its 16-bit tweaks are not silently admitted into the new whole-word syntax.
