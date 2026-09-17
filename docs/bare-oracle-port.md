# Porting the upper proof to the bare oracle (working notes, branch `bare-oracle`)

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
