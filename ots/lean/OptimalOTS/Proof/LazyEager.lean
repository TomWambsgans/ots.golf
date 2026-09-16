import OptimalOTS.Proof.LazyEagerDefs

/-!
# The lazy random oracle as a uniform table

Suppose every hash query of a computation decodes, injectively, to a cell of a finite type
`Cell`. Then running the computation with the lazy random oracle has the same output
distribution as first choosing a uniform table `g : Cell → BitVec hashBits` and answering every
hash query `q` with `g (dec q)`, while uniform sampling is forwarded unchanged.

The proof generalizes over the initial cache `c`: the lazy oracle started from `c` equals the
average over uniform tables `g` of `cacheTableImpl P dec c g`, which answers cached queries from
`c` and the others from `g`. On a cache miss, the fresh uniform answer is absorbed into the table
by `sum_sum_update`.
-/

open OracleSpec OracleComp ENNReal

noncomputable section

open scoped Classical

namespace OptimalOTS

/-- The table implementation overlaid with a cache: cached answers take priority. -/
def cacheTableImpl (P : Params) {Cell : Type} (dec : Query → Option Cell)
    (c : (hashSpec P).QueryCache) (g : Cell → BitVec P.hashBits) :
    QueryImpl (Spec P) ProbComp :=
  (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)) +
    (fun q => (pure ((c q).getD (match dec q with
      | some c => g c
      | none => 0)) : ProbComp (BitVec P.hashBits)) : QueryImpl (hashSpec P) ProbComp)

theorem cacheTableImpl_empty (P : Params) {Cell : Type} (dec : Query → Option Cell)
    (g : Cell → BitVec P.hashBits) :
    cacheTableImpl P dec ∅ g = tableImpl P dec g := rfl

theorem cacheTableImpl_inl (P : Params) {Cell : Type} (dec : Query → Option Cell)
    (c : (hashSpec P).QueryCache) (g : Cell → BitVec P.hashBits) (t : ℕ) :
    cacheTableImpl P dec c g (.inl t) = HasQuery.query (spec := unifSpec) (m := ProbComp) t := rfl

theorem cacheTableImpl_inr (P : Params) {Cell : Type} (dec : Query → Option Cell)
    (c : (hashSpec P).QueryCache) (g : Cell → BitVec P.hashBits) (q : Query) :
    cacheTableImpl P dec c g (.inr q) =
      pure ((c q).getD (match dec q with
        | some c => g c
        | none => 0)) := rfl

theorem oracleImpl_run_inl (P : Params) (c : (hashSpec P).QueryCache) (t : ℕ) :
    (oracleImpl P (.inl t)).run c =
      HasQuery.query (spec := unifSpec) (m := ProbComp) t >>= fun u => pure (u, c) := by
  simp [oracleImpl, StateT.run_monadLift]

theorem oracleImpl_run_inr_none (P : Params) {c : (hashSpec P).QueryCache} {q : Query}
    (hc : c q = none) :
    (oracleImpl P (.inr q)).run c =
      ($ᵗ BitVec P.hashBits) >>= fun u => pure (u, c.cacheQuery q u) := by
  have := randomOracle.run_eq (spec₀ := hashSpec P) q c
  rw [hc] at this
  exact this

theorem oracleImpl_run_inr_some (P : Params) {c : (hashSpec P).QueryCache} {q : Query}
    {u : BitVec P.hashBits} (hc : c q = some u) :
    (oracleImpl P (.inr q)).run c = pure (u, c) := by
  have := randomOracle.run_eq (spec₀ := hashSpec P) q c
  rw [hc] at this
  exact this

theorem cacheTableImpl_cacheQuery {P : Params} {Cell : Type} [DecidableEq Cell]
    (dec : Query → Option Cell)
    (hdec : ∀ q q' c, dec q = some c → dec q' = some c → q = q')
    {c : (hashSpec P).QueryCache} {q : Query} {cell : Cell} (hc : c q = none)
    (hq : dec q = some cell) (u : BitVec P.hashBits) (g : Cell → BitVec P.hashBits) :
    cacheTableImpl P dec (c.cacheQuery q u) g =
      cacheTableImpl P dec c (Function.update g cell u) := by
  funext t
  rcases t with t | q'
  · rfl
  · simp only [cacheTableImpl_inr]
    congr 1
    by_cases h : q' = q
    · subst h
      simp [hc, hq]
    · rw [QueryCache.cacheQuery_of_ne _ _ h]
      rcases hq' : dec q' with _ | cell'
      · rfl
      · have hne : cell' ≠ cell := fun e => h (hdec _ _ _ hq' (e ▸ hq))
        simp [Function.update_of_ne hne]

theorem sum_sum_update {Cell R : Type} [Fintype Cell] [DecidableEq Cell] [Fintype R]
    (H : (Cell → R) → ℝ≥0∞) (i : Cell) :
    ∑ u : R, ∑ g : Cell → R, H (Function.update g i u) = Fintype.card R * ∑ g, H g := by
  let φ : (Cell → R) × R → (Cell → R) × R := fun p => (Function.update p.1 i p.2, p.1 i)
  have hφ : Function.Involutive φ := by
    intro p
    simp [φ]
  rw [Finset.sum_comm, ← Fintype.sum_prod_type' (f := fun g u => H (Function.update g i u))]
  have := Equiv.sum_comp hφ.toPerm (fun p => H p.1)
  simp only [Function.Involutive.coe_toPerm, φ] at this
  rw [this, Fintype.sum_prod_type]
  simp [Finset.sum_const, nsmul_eq_mul, Finset.mul_sum, mul_comm]

theorem run'_bind_eq {σ α β : Type} (ma : StateT σ ProbComp α) (f : α → StateT σ ProbComp β)
    (s : σ) : (ma >>= f).run' s = ma.run s >>= fun p => (f p.1).run' p.2 := by
  simp [StateT.run'_eq, StateT.run_bind, map_bind]

theorem probOutput_oracleImpl_run'_eq_sum_cacheTable {P : Params} {Cell : Type} [Fintype Cell]
    (dec : Query → Option Cell) (hdec : ∀ q q' c, dec q = some c → dec q' = some c → q = q')
    {α : Type} (oa : OracleComp (Spec P) α) (hoa : HashQueriesIn dec oa)
    (c : (hashSpec P).QueryCache) (x : α) :
    Pr[= x | (simulateQ (oracleImpl P) oa).run' c] =
      (∑ g : Cell → BitVec P.hashBits, Pr[= x | simulateQ (cacheTableImpl P dec c g) oa]) /
        (Fintype.card (Cell → BitVec P.hashBits) : ℝ≥0∞) := by
  have hN0 : (Fintype.card (Cell → BitVec P.hashBits) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hNt : (Fintype.card (Cell → BitVec P.hashBits) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  induction oa using OracleComp.inductionOn generalizing c with
  | pure a =>
    simp only [simulateQ_pure, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [mul_comm, ENNReal.mul_div_cancel_right hN0 hNt]
    rfl
  | query_bind t k ih =>
    rw [HashQueriesIn, allQueriesSatisfy_query_bind_iff] at hoa
    obtain ⟨ht, hk⟩ := hoa
    have ih' := fun u c => ih u (hk u) c
    clear ih
    rw [simulateQ_bind, simulateQ_spec_query, run'_bind_eq]
    simp only [simulateQ_bind, simulateQ_spec_query]
    rcases t with t | q
    · simp only [oracleImpl_run_inl, cacheTableImpl_inl, bind_assoc, pure_bind,
        probOutput_bind_eq_tsum, ih']
      simp only [div_eq_mul_inv, Finset.sum_mul, ← ENNReal.tsum_mul_right]
      rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
      refine tsum_congr fun u => ?_
      simp only [Finset.mul_sum, mul_assoc]
    · let _ : DecidableEq Cell := fun a b => Classical.propDecidable (a = b)
      obtain ⟨cell, hq⟩ := Option.isSome_iff_exists.1 ht
      simp only [cacheTableImpl_inr, pure_bind]
      rcases hc : c q with _ | u
      · have hn0 : (Fintype.card (BitVec P.hashBits) : ℝ≥0∞) ≠ 0 := by
          exact_mod_cast Fintype.card_ne_zero
        have hnt : (Fintype.card (BitVec P.hashBits) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
        simp only [oracleImpl_run_inr_none P hc, bind_assoc, pure_bind, probOutput_bind_eq_tsum,
          probOutput_uniformSample, ih', cacheTableImpl_cacheQuery dec hdec hc hq, hq,
          Option.getD_none, tsum_fintype]
        have key := sum_sum_update
          (fun g => Pr[= x | simulateQ (cacheTableImpl P dec c g) (k (g cell))]) cell
        simp only [Function.update_self] at key
        have key' : (∑ g : Cell → BitVec P.hashBits,
            Pr[= x | simulateQ (cacheTableImpl P dec c g) (k (g cell))]) =
            (Fintype.card (BitVec P.hashBits) : ℝ≥0∞)⁻¹ *
              ∑ u : BitVec P.hashBits, ∑ g : Cell → BitVec P.hashBits,
                Pr[= x | simulateQ (cacheTableImpl P dec c (Function.update g cell u)) (k u)] := by
          rw [key, ← mul_assoc, ENNReal.inv_mul_cancel hn0 hnt, one_mul]
        erw [key']
        simp only [div_eq_mul_inv, Finset.mul_sum, Finset.sum_mul, mul_assoc]
      · simp only [oracleImpl_run_inr_some P hc, pure_bind, ih', Option.getD_some]

/-- The lazy random oracle equals a uniform table on the decoded cells. -/
theorem probOutput_oracleImpl_eq_sum_table {P : Params} {Cell : Type} [Fintype Cell]
    (dec : Query → Option Cell) (hdec : ∀ q q' c, dec q = some c → dec q' = some c → q = q')
    {α : Type} (oa : OracleComp (Spec P) α) (hoa : HashQueriesIn dec oa) (x : α) :
    Pr[= x | (simulateQ (oracleImpl P) oa).run' ∅] =
      (∑ g : Cell → BitVec P.hashBits, Pr[= x | simulateQ (tableImpl P dec g) oa]) /
        (Fintype.card (Cell → BitVec P.hashBits) : ℝ≥0∞) :=
  probOutput_oracleImpl_run'_eq_sum_cacheTable dec hdec oa hoa ∅ x

end OptimalOTS
