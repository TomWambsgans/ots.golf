import Witnesses.Generality2.Master

/-!
# The signing loop

`signIdx P m` is the signing loop returning the selected nonce and index instead of the
signature; `Scheme.sign` is its image under encoding the revealed values.

The analysis of the loop, started from a cache `d`:

* `run_signIdx_extend`: cache entries of other lengths are irrelevant to the loop;
* `signIdx_support`: every new cache entry is an encoding entry at an input `m ++ η`; a new
  entry with a valid index is the one that ended the loop;
* the signing bound's vocabulary, used by the disjoint signing lemma of `SignRho.lean`:
  `IdxPre d u₁ i` (a pre-existing encoding entry `u ≠ u₁` has index `i`), `SignExt` (the
  entries added by a run with a given outcome), the valid indices `V d` of the cache, and the
  one-trial facts `signExt_none`, `signExt_cached`, `signExt_fresh`, `ind_le_V`.
-/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal

noncomputable section

open scoped Classical

namespace OptimalOTS

/-! ## Lemmas shared with the lower-bound proof (copied: submissions may not import each other) -/

namespace Analysis

lemma setWidth_append_nonce {P : Params} {F : DagFormat} (m : Message P) (η : Nonce F) :
    (m ++ η).setWidth F.nonceBits = η := by
  ext j hj
  simp [BitVec.getElem_setWidth, BitVec.getLsbD_append, hj]

lemma sum_fin_equivFin {α : Type*} {s : Finset α} {n : ℕ} (h : n = s.card) (G : α → ℝ≥0∞) :
    ∑ j : Fin n, G (s.equivFin.symm (Fin.cast h j)).1 = ∑ η ∈ s, G η := by
  rw [← Finset.sum_coe_sort s]
  exact Equiv.sum_comp ((finCongr h).trans s.equivFin.symm) (fun x => G x.1)

/-- The index read from an oracle output. -/
def idxOfOut (P : Params) (F : DagFormat) (y : BitVec P.hashBits) : ℕ := (y.setWidth F.idxBits).toNat

/-- Number of oracle outputs whose index lies in a set of index values. -/
theorem card_idxOfOut_mem {P : Params} {F : DagFormat} (hidx : F.idxBits ≤ P.hashBits) (A : Finset ℕ)
    (hA : ∀ n ∈ A, n < 2 ^ F.idxBits) :
    (Finset.univ.filter fun y : BitVec P.hashBits => idxOfOut P F y ∈ A).card =
      A.card * 2 ^ (P.hashBits - F.idxBits) := by
  have hH : 2 ^ P.hashBits = 2 ^ F.idxBits * 2 ^ (P.hashBits - F.idxBits) := by
    rw [← pow_add, Nat.add_sub_cancel' hidx]
  have hNpos : 0 < 2 ^ F.idxBits := by positivity
  rw [← Finset.card_range (2 ^ (P.hashBits - F.idxBits)), ← Finset.card_product]
  refine Finset.card_nbij' (fun y => (y.toNat % 2 ^ F.idxBits, y.toNat / 2 ^ F.idxBits))
    (fun x => BitVec.ofNat P.hashBits (x.1 + 2 ^ F.idxBits * x.2)) ?_ ?_ ?_ ?_
  · intro y hy
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hy
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_range]
    refine ⟨?_, ?_⟩
    · simpa [idxOfOut, BitVec.toNat_setWidth] using hy
    · rw [Nat.div_lt_iff_lt_mul hNpos]
      have := y.isLt
      rw [hH] at this
      linarith
  · intro x hx
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_range] at hx
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
    have h1 : x.1 + 2 ^ F.idxBits * x.2 < 2 ^ P.hashBits := by
      rw [hH]
      have := hA _ hx.1
      nlinarith
    simp only [idxOfOut, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (hA _ hx.1)]
    exact hx.1
  · intro y _
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat]
    rw [Nat.mod_add_div, Nat.mod_eq_of_lt y.isLt]
  · intro x hx
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_range] at hx
    have hx1 := hA _ hx.1
    have h1 : x.1 + 2 ^ F.idxBits * x.2 < 2 ^ P.hashBits := by
      rw [hH]
      nlinarith
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt hx1, Nat.add_mul_div_left _ _ hNpos, Nat.div_eq_of_lt hx1, zero_add]

end Analysis


variable (P : Params) (F : DagFormat)

/-- An encoding input. -/
abbrev EncInput (P : Params) (F : DagFormat) := BitVec (P.msgBits + F.nonceBits)

/-- The encoding query at input `u`: the query of length `msgBits + nonceBits` with bits `u`. The
oracle has no labels, so an encoding query is told apart from every other query by its length. -/
def encQuery (u : EncInput P F) : Query := ⟨P.msgBits + F.nonceBits, u⟩

/-- The index read from an oracle answer. -/
def idxOf (w : BitVec P.hashBits) : ℕ := (w.setWidth F.idxBits).toNat

/-- The signing loop, returning the nonce and the index. -/
def signIdxLoop (m : Message P) :
    ℕ → Finset (Nonce F) → OracleComp (Spec P) (Option (Nonce F × Fin F.numSets))
  | 0, _ => pure none
  | k + 1, tried =>
    let fresh := Finset.univ \ tried
    if h : 0 < fresh.card then do
      let j ← (liftM ($[0..(fresh.card - 1)]) : OracleComp (Spec P) (Fin (fresh.card - 1 + 1)))
      let η : Nonce F := (fresh.equivFin.symm (Fin.cast (by omega) j)).1
      let i ← index P F m η
      if hi : i < F.numSets then
        return some (η, ⟨i, hi⟩)
      else
        signIdxLoop m k (insert η tried)
    else
      pure none

/-- Signing, returning the nonce and the index. -/
def signIdx (m : Message P) : OracleComp (Spec P) (Option (Nonce F × Fin F.numSets)) :=
  signIdxLoop P F m F.trialLimit ∅

/-! ### Basic facts on encoding inputs -/

theorem encQuery_inj {u u' : EncInput P F} (h : encQuery P F u = encQuery P F u') : u = u' := by
  simp only [encQuery, Sigma.mk.inj_iff, heq_eq_eq, true_and] at h
  exact h

/-- A query of another length is not an encoding query. -/
theorem ne_encQuery_of_length_ne {q : Query} (hq : q.1 ≠ P.msgBits + F.nonceBits)
    (u : EncInput P F) : q ≠ encQuery P F u := by
  rintro rfl
  exact hq rfl

/-- The queries of encoding length are exactly the encoding queries. -/
theorem exists_eq_encQuery_of_length_eq {q : Query} (hq : q.1 = P.msgBits + F.nonceBits) :
    ∃ u : EncInput P F, q = encQuery P F u := by
  obtain ⟨k, v⟩ := q
  change k = P.msgBits + F.nonceBits at hq
  subst hq
  exact ⟨v, rfl⟩

theorem append_nonce_inj (m : Message P) {η η' : Nonce F} (h : m ++ η = m ++ η') : η = η' := by
  have := congrArg (fun u : EncInput P F => u.setWidth F.nonceBits) h
  simpa only [Analysis.setWidth_append_nonce] using this

/-! ### The loop in query normal form -/

theorem liftM_uniformFin_eq (n : ℕ) :
    (liftM ($[0..n]) : OracleComp (Spec P) (Fin (n + 1))) =
      liftM ((Spec P).query (.inl n)) := by
  change liftComp ($[0..n]) (Spec P) = _
  simp [liftComp, ProbComp.uniformFin]
  rfl

/-- The continuation of the loop after the encoding answer `w` at nonce `η`. -/
def afterHash (m : Message P) (k : ℕ) (tried : Finset (Nonce F)) (η : Nonce F)
    (w : BitVec P.hashBits) : OracleComp (Spec P) (Option (Nonce F × Fin F.numSets)) :=
  if hi : idxOf P F w < F.numSets then pure (some (η, ⟨idxOf P F w, hi⟩))
  else signIdxLoop P F m k (insert η tried)

/-- The body of the loop at nonce `η`: one encoding query, then stop or recurse. -/
def loopBody (m : Message P) (k : ℕ) (tried : Finset (Nonce F)) (η : Nonce F) :
    OracleComp (Spec P) (Option (Nonce F × Fin F.numSets)) :=
  (liftM ((Spec P).query (.inr (encQuery P F (m ++ η)))) :
      OracleComp (Spec P) (BitVec P.hashBits)) >>= afterHash P F m k tried η

/-- The nonce selected by the sample `j`. -/
def nonceOf (tried : Finset (Nonce F)) (hc : 0 < (Finset.univ \ tried).card)
    (j : Fin ((Finset.univ \ tried).card - 1 + 1)) : Nonce F :=
  ((Finset.univ \ tried).equivFin.symm (Fin.cast (by omega) j)).1

theorem nonceOf_mem (tried : Finset (Nonce F)) (hc : 0 < (Finset.univ \ tried).card)
    (j : Fin ((Finset.univ \ tried).card - 1 + 1)) :
    nonceOf F tried hc j ∈ Finset.univ \ tried :=
  ((Finset.univ \ tried).equivFin.symm (Fin.cast (by omega) j)).2

theorem signIdxLoop_succ (m : Message P) (k : ℕ) (tried : Finset (Nonce F))
    (hc : 0 < (Finset.univ \ tried).card) :
    signIdxLoop P F m (k + 1) tried =
      (liftM ((Spec P).query (.inl ((Finset.univ \ tried).card - 1))) :
          OracleComp (Spec P) (Fin ((Finset.univ \ tried).card - 1 + 1))) >>= fun j =>
        loopBody P F m k tried (nonceOf F tried hc j) := by
  rw [signIdxLoop, dif_pos hc, liftM_uniformFin_eq]
  refine bind_congr fun j => ?_
  simp only [loopBody, nonceOf, index, hash, map_eq_bind_pure_comp, bind_assoc, pure_bind,
    Function.comp_def]
  rfl

/-! ### One-step lemmas -/

theorem costAtMost_inl_bind {α β : Type} (t : ℕ)
    (body : Fin (t + 1) → OracleComp (Spec P) α) (kont : α → OracleComp (Spec P) β) {b : ℕ}
    (h : CostAtMost P (((liftM ((Spec P).query (.inl t)) : OracleComp (Spec P) (Fin (t + 1)))
      >>= body) >>= kont) b) :
    ∀ j, CostAtMost P (body j >>= kont) b := by
  rw [bind_assoc, costAtMost_query_bind_iff] at h
  intro j
  have := h.2 j
  rwa [show queryCost P (.inl t) = 0 from rfl, Nat.sub_zero] at this

theorem costAtMost_inr_bind {α β : Type} (q : Query)
    (body : BitVec P.hashBits → OracleComp (Spec P) α) (kont : α → OracleComp (Spec P) β)
    {b : ℕ}
    (h : CostAtMost P (((liftM ((Spec P).query (.inr q)) : OracleComp (Spec P) (BitVec P.hashBits))
      >>= body) >>= kont) b) :
    queryCost P (.inr q) ≤ b ∧
      ∀ w, CostAtMost P (body w >>= kont) (b - queryCost P (.inr q)) := by
  rw [bind_assoc, costAtMost_query_bind_iff] at h
  exact h

theorem mem_support_run_inl {α : Type} {t : ℕ} {body : Fin (t + 1) → OracleComp (Spec P) α}
    {c : Cache P} {p : α × Cache P}
    (hp : p ∈ support (run P ((liftM ((Spec P).query (.inl t)) :
      OracleComp (Spec P) (Fin (t + 1))) >>= body) c)) :
    ∃ j, p ∈ support (run P (body j) c) := by
  rw [run_query_bind, support_bind] at hp
  simp only [Set.mem_iUnion] at hp
  obtain ⟨⟨u, c'⟩, hu, hp⟩ := hp
  rw [oracleImpl_run_inl, support_bind] at hu
  simp only [Set.mem_iUnion] at hu
  obtain ⟨w, -, hw⟩ := hu
  simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hw
  obtain ⟨rfl, rfl⟩ := hw
  exact ⟨u, hp⟩

theorem mem_support_run_inr_none {α : Type} {q : Query}
    {body : BitVec P.hashBits → OracleComp (Spec P) α} {c : Cache P} {p : α × Cache P}
    (hc : c q = none)
    (hp : p ∈ support (run P ((liftM ((Spec P).query (.inr q)) :
      OracleComp (Spec P) (BitVec P.hashBits)) >>= body) c)) :
    ∃ w, p ∈ support (run P (body w) (c.cacheQuery q w)) := by
  rw [run_query_bind, support_bind] at hp
  simp only [Set.mem_iUnion] at hp
  obtain ⟨⟨u, c'⟩, hu, hp⟩ := hp
  rw [oracleImpl_run_inr_none P hc, support_bind] at hu
  simp only [Set.mem_iUnion] at hu
  obtain ⟨w, -, hw⟩ := hu
  simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hw
  obtain ⟨rfl, rfl⟩ := hw
  exact ⟨u, hp⟩

theorem mem_support_run_inr_some {α : Type} {q : Query} {u : BitVec P.hashBits}
    {body : BitVec P.hashBits → OracleComp (Spec P) α} {c : Cache P} {p : α × Cache P}
    (hc : c q = some u)
    (hp : p ∈ support (run P ((liftM ((Spec P).query (.inr q)) :
      OracleComp (Spec P) (BitVec P.hashBits)) >>= body) c)) :
    p ∈ support (run P (body u) c) := by
  rw [run_query_bind, support_bind] at hp
  simp only [Set.mem_iUnion] at hp
  obtain ⟨⟨u', c'⟩, hu, hp⟩ := hp
  rw [oracleImpl_run_inr_some P hc, support_pure] at hu
  simp only [Set.mem_singleton_iff, Prod.mk.injEq] at hu
  obtain ⟨rfl, rfl⟩ := hu
  exact hp

/-! ### `Scheme.sign` as the image of `signIdx` -/

theorem signLoop_eq_map {P : Params} {F : DagFormat} (S : Scheme P F) (x : S.graph.Assignment) (m : Message P) :
    ∀ (k : ℕ) (tried : Finset (Nonce F)),
      S.signLoop x m k tried =
        (Option.map fun r : Nonce F × Fin F.numSets => (r.1, S.graph.encode (S.sets r.2) x)) <$>
          signIdxLoop P F m k tried := by
  intro k
  induction k with
  | zero => intro tried; simp [Scheme.signLoop, signIdxLoop]
  | succ k ih =>
    intro tried
    by_cases hc : 0 < (Finset.univ \ tried).card
    · rw [Scheme.signLoop, signIdxLoop, dif_pos hc, dif_pos hc]
      simp only [map_bind]
      refine bind_congr fun j => ?_
      refine bind_congr fun i => ?_
      split_ifs with hi
      · simp
      · exact ih _
    · rw [Scheme.signLoop, signIdxLoop, dif_neg hc, dif_neg hc]
      simp

/-- `Scheme.sign` encodes the revealed values of the index found by `signIdx`. -/
theorem sign_eq_map {P : Params} {F : DagFormat} (S : Scheme P F) (x : S.graph.Assignment) (m : Message P) :
    S.sign x m =
      (Option.map fun r : Nonce F × Fin F.numSets => (r.1, S.graph.encode (S.sets r.2) x)) <$>
        signIdx P F m :=
  signLoop_eq_map S x m F.trialLimit ∅

/-! ### Non-encoding entries are irrelevant -/

theorem run_signIdxLoop_extend (m : Message P) (f : Cache P)
    (hf : ∀ u : EncInput P F, f (encQuery P F u) = none) :
    ∀ (k : ℕ) (tried : Finset (Nonce F)) (d : Cache P),
      run P (signIdxLoop P F m k tried) (Cache.extend d f) =
        (fun p => (p.1, Cache.extend p.2 f)) <$> run P (signIdxLoop P F m k tried) d := by
  intro k
  induction k with
  | zero => intro tried d; simp [signIdxLoop, run_pure]
  | succ k ih =>
    intro tried d
    by_cases hc : 0 < (Finset.univ \ tried).card
    · rw [signIdxLoop_succ P F m k tried hc, run_query_bind, run_query_bind, oracleImpl_run_inl,
        oracleImpl_run_inl]
      simp only [bind_assoc, pure_bind, map_bind]
      refine bind_congr fun j => ?_
      simp only [loopBody]
      rw [run_query_bind, run_query_bind]
      rcases hdq : d (encQuery P F (m ++ nonceOf F tried hc j)) with _ | w
      · have hdq' : Cache.extend d f (encQuery P F (m ++ nonceOf F tried hc j)) = none := by
          rw [Cache.extend_apply_of_none hdq]; exact hf _
        rw [oracleImpl_run_inr_none P hdq, oracleImpl_run_inr_none P hdq']
        simp only [bind_assoc, pure_bind, map_bind]
        refine bind_congr fun w => ?_
        rw [← Cache.extend_cacheQuery]
        simp only [afterHash]
        split_ifs with hi
        · simp [run_pure]
        · exact ih _ _
      · have hdq' : Cache.extend d f (encQuery P F (m ++ nonceOf F tried hc j)) = some w :=
          Cache.extend_apply_of_some hdq
        rw [oracleImpl_run_inr_some P hdq, oracleImpl_run_inr_some P hdq', pure_bind, pure_bind]
        simp only [afterHash]
        split_ifs with hi
        · simp [run_pure]
        · exact ih _ _
    · rw [signIdxLoop, dif_neg hc]
      simp [run_pure]

/-- Entries at non-encoding points (queries of another length) are irrelevant to the loop. -/
theorem run_signIdx_extend (m : Message P) (d f : Cache P)
    (hf : ∀ u : EncInput P F, f (encQuery P F u) = none) :
    run P (signIdx P F m) (Cache.extend d f) =
      (fun p => (p.1, Cache.extend p.2 f)) <$> run P (signIdx P F m) d :=
  run_signIdxLoop_extend P F m f hf F.trialLimit ∅ d

/-! ### The new cache entries -/

theorem signIdxLoop_support (m : Message P) :
    ∀ (k : ℕ) (tried : Finset (Nonce F)) (d : Cache P),
      ∀ p ∈ support (run P (signIdxLoop P F m k tried) d),
        Cache.Sub d p.2 ∧
        (∀ q w, d q = none → p.2 q = some w →
          ∃ η : Nonce F, q = encQuery P F (m ++ η) ∧
            ∀ hi : idxOf P F w < F.numSets, p.1 = some (η, ⟨idxOf P F w, hi⟩)) ∧
        (∀ η i, p.1 = some (η, i) →
          ∃ w, p.2 (encQuery P F (m ++ η)) = some w ∧ idxOf P F w = i.val) := by
  intro k
  induction k with
  | zero =>
    intro tried d p hp
    rw [signIdxLoop, run_pure, support_pure] at hp
    simp only [Set.mem_singleton_iff] at hp
    subst hp
    refine ⟨Cache.Sub.refl d, fun q w h1 h2 => ?_, fun η i h => by simp at h⟩
    change d q = some w at h2
    rw [h1] at h2; cases h2
  | succ k ih =>
    intro tried d p hp
    by_cases hc : 0 < (Finset.univ \ tried).card
    · rw [signIdxLoop_succ P F m k tried hc] at hp
      obtain ⟨j, hp⟩ := mem_support_run_inl P hp
      simp only [loopBody] at hp
      generalize nonceOf F tried hc j = η at hp
      rcases hdq : d (encQuery P F (m ++ η)) with _ | w
      · obtain ⟨w, hp⟩ := mem_support_run_inr_none P hdq hp
        rw [afterHash] at hp
        by_cases hi : idxOf P F w < F.numSets
        · rw [dif_pos hi, run_pure, support_pure] at hp
          simp only [Set.mem_singleton_iff] at hp
          subst hp
          refine ⟨Cache.sub_cacheQuery_of_none hdq w, ?_, ?_⟩
          · intro q w' h1 h2
            change (d.cacheQuery (encQuery P F (m ++ η)) w) q = some w' at h2
            by_cases hq : q = encQuery P F (m ++ η)
            · subst hq
              rw [QueryCache.cacheQuery_self] at h2
              obtain rfl := Option.some.inj h2
              exact ⟨η, rfl, fun _ => rfl⟩
            · rw [QueryCache.cacheQuery_of_ne _ _ hq, h1] at h2
              cases h2
          · intro η' i h
            change some (η, ⟨idxOf P F w, hi⟩) = some (η', i) at h
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            exact ⟨w, QueryCache.cacheQuery_self _ _ _, rfl⟩
        · rw [dif_neg hi] at hp
          obtain ⟨h1, h2, h3⟩ := ih (insert η tried) (d.cacheQuery _ w) p hp
          refine ⟨(Cache.sub_cacheQuery_of_none hdq w).trans h1, ?_, h3⟩
          intro q w' hq1 hq2
          by_cases hq : q = encQuery P F (m ++ η)
          · subst hq
            have : p.2 (encQuery P F (m ++ η)) = some w :=
              h1 _ _ (QueryCache.cacheQuery_self _ _ _)
            rw [this] at hq2
            obtain rfl := Option.some.inj hq2
            exact ⟨η, rfl, fun hi' => absurd hi' hi⟩
          · exact h2 q w' (by rw [QueryCache.cacheQuery_of_ne _ _ hq]; exact hq1) hq2
      · have hp := mem_support_run_inr_some P hdq hp
        rw [afterHash] at hp
        by_cases hi : idxOf P F w < F.numSets
        · rw [dif_pos hi, run_pure, support_pure] at hp
          simp only [Set.mem_singleton_iff] at hp
          subst hp
          refine ⟨Cache.Sub.refl d, fun q w' h1 h2 => ?_, ?_⟩
          · change d q = some w' at h2
            rw [h1] at h2; cases h2
          · intro η' i h
            change some (η, ⟨idxOf P F w, hi⟩) = some (η', i) at h
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            exact ⟨w, hdq, rfl⟩
        · rw [dif_neg hi] at hp
          exact ih (insert η tried) d p hp
    · rw [signIdxLoop, dif_neg hc, run_pure, support_pure] at hp
      simp only [Set.mem_singleton_iff] at hp
      subst hp
      refine ⟨Cache.Sub.refl d, fun q w h1 h2 => ?_, fun η i h => by simp at h⟩
      change d q = some w at h2
      rw [h1] at h2; cases h2

/-- The new cache entries of the loop. -/
theorem signIdx_support (m : Message P) (d : Cache P) :
    ∀ p ∈ support (run P (signIdx P F m) d),
      Cache.Sub d p.2 ∧
      (∀ q w, d q = none → p.2 q = some w →
        ∃ η : Nonce F, q = encQuery P F (m ++ η) ∧
          ∀ hi : idxOf P F w < F.numSets, p.1 = some (η, ⟨idxOf P F w, hi⟩)) ∧
      (∀ η i, p.1 = some (η, i) → ∃ w, p.2 (encQuery P F (m ++ η)) = some w ∧ idxOf P F w = i.val) :=
  signIdxLoop_support P F m F.trialLimit ∅ d

/-! ### The signing bound -/

/-- A pre-existing encoding entry other than `u₁` has index `i`. -/
def IdxPre (d : Cache P) (u₁ : EncInput P F) (i : ℕ) : Prop :=
  ∃ u, u ≠ u₁ ∧ ∃ w, d (encQuery P F u) = some w ∧ idxOf P F w = i

/-- `Φ` does not see encoding entries: the entries at queries of length `msgBits + nonceBits`. -/
def EncInvariant (Φ : Cache P → ℝ≥0∞) : Prop :=
  ∀ (c : Cache P) (u : EncInput P F) (w : BitVec P.hashBits),
    Φ (c.cacheQuery (encQuery P F u) w) = Φ c

/-- `d'` extends `d` by the entries of a signing run with outcome `r`. -/
def SignExt (m : Message P) (d : Cache P) (r : Option (Nonce F × Fin F.numSets)) (d' : Cache P) :
    Prop :=
  Cache.Sub d d' ∧
  (∀ q w, d q = none → d' q = some w →
    ∃ η : Nonce F, q = encQuery P F (m ++ η) ∧
      ∀ hi : idxOf P F w < F.numSets, r = some (η, ⟨idxOf P F w, hi⟩)) ∧
  (∀ η i, r = some (η, i) → ∃ w, d' (encQuery P F (m ++ η)) = some w ∧ idxOf P F w = i.val)

/-- The encoding inputs cached with a valid index. -/
def validSet (d : Cache P) : Finset (EncInput P F) :=
  Finset.univ.filter fun u : EncInput P F => ∃ w, d (encQuery P F u) = some w ∧ idxOf P F w < F.numSets

/-- The valid indices of the entries of `d`. -/
def V (d : Cache P) : Finset ℕ :=
  (validSet P F d).image fun u => ((d (encQuery P F u)).map (idxOf P F)).getD 0

theorem mem_V {d : Cache P} {u : EncInput P F} {w : BitVec P.hashBits}
    (hu : d (encQuery P F u) = some w) (hw : idxOf P F w < F.numSets) : idxOf P F w ∈ V P F d := by
  refine Finset.mem_image.2 ⟨u, ?_, ?_⟩
  · simp only [validSet, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨w, hu, hw⟩
  · simp [hu]

theorem V_lt (d : Cache P) : ∀ n ∈ V P F d, n < 2 ^ F.idxBits := by
  intro n hn
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hn
  simp only [validSet, Finset.mem_filter, Finset.mem_univ, true_and] at hu
  obtain ⟨w, hw, -⟩ := hu
  simp only [hw, Option.map_some, Option.getD_some]
  exact (w.setWidth F.idxBits).isLt

theorem card_idxOf_mem (hidx : F.idxBits ≤ P.hashBits) (A : Finset ℕ)
    (hA : ∀ n ∈ A, n < 2 ^ F.idxBits) :
    (Finset.univ.filter fun y : BitVec P.hashBits => idxOf P F y ∈ A).card =
      A.card * 2 ^ (P.hashBits - F.idxBits) :=
  Analysis.card_idxOfOut_mem hidx A hA

theorem E_query_unif (n : ℕ) (g : Fin (n + 1) → ℝ≥0∞) :
    E (HasQuery.query (spec := unifSpec) (m := ProbComp) n) g =
      ∑ j, ((n : ℝ≥0∞) + 1)⁻¹ * g j := by
  rw [E, expectedValue_def, tsum_fintype]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  exact ProbComp.probOutput_uniformFin n j

theorem cache_eq_of_notMem {d d' : Cache P} {m : Message P} {tried : Finset (Nonce F)}
    (hSub : Cache.Sub d d')
    (hNew : ∀ q w, d q = none → d' q = some w →
      ∃ η ∈ tried, q = encQuery P F (m ++ η) ∧ ¬ idxOf P F w < F.numSets)
    {η : Nonce F} (hη : η ∉ tried) :
    d' (encQuery P F (m ++ η)) = d (encQuery P F (m ++ η)) := by
  rcases hdq : d (encQuery P F (m ++ η)) with _ | w
  · rcases hd'q : d' (encQuery P F (m ++ η)) with _ | w'
    · rfl
    · obtain ⟨η', hη', he, -⟩ := hNew _ _ hdq hd'q
      exact absurd (by rw [append_nonce_inj P F m (encQuery_inj P F he)]; exact hη') hη
  · exact hSub _ _ hdq

theorem new_cacheQuery {d d' : Cache P} {m : Message P} {tried : Finset (Nonce F)}
    (hNew : ∀ q w, d q = none → d' q = some w →
      ∃ η ∈ tried, q = encQuery P F (m ++ η) ∧ ¬ idxOf P F w < F.numSets)
    (η : Nonce F) {w : BitVec P.hashBits} (hw : ¬ idxOf P F w < F.numSets) :
    ∀ q w', d q = none → (d'.cacheQuery (encQuery P F (m ++ η)) w) q = some w' →
      ∃ η' ∈ insert η tried, q = encQuery P F (m ++ η') ∧ ¬ idxOf P F w' < F.numSets := by
  intro q w' h1 h2
  by_cases hq : q = encQuery P F (m ++ η)
  · subst hq
    rw [QueryCache.cacheQuery_self] at h2
    obtain rfl := Option.some.inj h2
    exact ⟨η, Finset.mem_insert_self _ _, rfl, hw⟩
  · rw [QueryCache.cacheQuery_of_ne _ _ hq] at h2
    obtain ⟨η', hη', he, hi⟩ := hNew q w' h1 h2
    exact ⟨η', Finset.mem_insert_of_mem hη', he, hi⟩

theorem new_insert {d d' : Cache P} {m : Message P} {tried : Finset (Nonce F)}
    (hNew : ∀ q w, d q = none → d' q = some w →
      ∃ η ∈ tried, q = encQuery P F (m ++ η) ∧ ¬ idxOf P F w < F.numSets)
    (η : Nonce F) :
    ∀ q w, d q = none → d' q = some w →
      ∃ η' ∈ insert η tried, q = encQuery P F (m ++ η') ∧ ¬ idxOf P F w < F.numSets :=
  fun q w h1 h2 =>
    let ⟨η', hη', he, hi⟩ := hNew q w h1 h2
    ⟨η', Finset.mem_insert_of_mem hη', he, hi⟩

theorem signExt_none {d d' : Cache P} {m : Message P} {tried : Finset (Nonce F)}
    (hSub : Cache.Sub d d')
    (hNew : ∀ q w, d q = none → d' q = some w →
      ∃ η ∈ tried, q = encQuery P F (m ++ η) ∧ ¬ idxOf P F w < F.numSets) :
    SignExt P F m d none d' := by
  unfold SignExt
  refine ⟨hSub, fun q w h1 h2 => ?_, fun η i h => by cases h⟩
  obtain ⟨η, -, he, hi⟩ := hNew q w h1 h2
  exact ⟨η, he, fun hi' => absurd hi' hi⟩

theorem signExt_cached {d d' : Cache P} {m : Message P} {tried : Finset (Nonce F)}
    (hSub : Cache.Sub d d')
    (hNew : ∀ q w, d q = none → d' q = some w →
      ∃ η ∈ tried, q = encQuery P F (m ++ η) ∧ ¬ idxOf P F w < F.numSets)
    {η : Nonce F} {w : BitVec P.hashBits} (hi : idxOf P F w < F.numSets)
    (hq : d' (encQuery P F (m ++ η)) = some w) :
    SignExt P F m d (some (η, ⟨idxOf P F w, hi⟩)) d' := by
  unfold SignExt
  refine ⟨hSub, fun q w' h1 h2 => ?_, fun η' i h => ?_⟩
  · obtain ⟨η', -, he, hi'⟩ := hNew q w' h1 h2
    exact ⟨η', he, fun h => absurd h hi'⟩
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨w, hq, rfl⟩

theorem signExt_fresh {d d' : Cache P} {m : Message P} {tried : Finset (Nonce F)}
    (hSub : Cache.Sub d d')
    (hNew : ∀ q w, d q = none → d' q = some w →
      ∃ η ∈ tried, q = encQuery P F (m ++ η) ∧ ¬ idxOf P F w < F.numSets)
    {η : Nonce F} {w : BitVec P.hashBits} (hi : idxOf P F w < F.numSets)
    (hq : d' (encQuery P F (m ++ η)) = none) :
    SignExt P F m d (some (η, ⟨idxOf P F w, hi⟩)) (d'.cacheQuery (encQuery P F (m ++ η)) w) := by
  unfold SignExt
  refine ⟨hSub.trans (Cache.sub_cacheQuery_of_none hq w), fun q w' h1 h2 => ?_,
    fun η' i h => ?_⟩
  · by_cases hqe : q = encQuery P F (m ++ η)
    · subst hqe
      rw [QueryCache.cacheQuery_self] at h2
      obtain rfl := Option.some.inj h2
      exact ⟨η, rfl, fun _ => rfl⟩
    · rw [QueryCache.cacheQuery_of_ne _ _ hqe] at h2
      obtain ⟨η', -, he, hi'⟩ := hNew q w' h1 h2
      exact ⟨η', he, fun h => absurd h hi'⟩
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨w, QueryCache.cacheQuery_self _ _ _, rfl⟩

theorem ind_le_V {d : Cache P} {m : Message P} {η : Nonce F} {w : BitVec P.hashBits}
    (hi : idxOf P F w < F.numSets) :
    (if ∃ η' i, (some (η, ⟨idxOf P F w, hi⟩) : Option (Nonce F × Fin F.numSets)) = some (η', i) ∧
        IdxPre P F d (m ++ η') i.val then (1 : ℝ≥0∞) else 0) ≤
      if idxOf P F w ∈ V P F d then 1 else 0 := by
  by_cases h1 : ∃ η' i, (some (η, ⟨idxOf P F w, hi⟩) : Option (Nonce F × Fin F.numSets)) =
      some (η', i) ∧ IdxPre P F d (m ++ η') i.val
  · rw [if_pos h1]
    obtain ⟨η', i, he, hpre⟩ := h1
    simp only [Option.some.injEq, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    obtain ⟨u, -, w', hu, hw'⟩ := hpre
    have hw'' : idxOf P F w' = idxOf P F w := hw'
    have := mem_V P F hu (by rw [hw'']; exact hi)
    rw [hw''] at this
    rw [if_pos this]
  · rw [if_neg h1]; exact zero_le

theorem not_exists_none {d : Cache P} {m : Message P} :
    ¬ ∃ (η : Nonce F) (i : Fin F.numSets),
      (none : Option (Nonce F × Fin F.numSets)) = some (η, i) ∧ IdxPre P F d (m ++ η) i.val := by
  rintro ⟨_, _, h, _⟩
  cases h

end OptimalOTS
