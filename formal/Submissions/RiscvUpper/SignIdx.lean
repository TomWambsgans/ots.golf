import Submissions.RiscvUpper.Master

/-!
# The signing loop

`signIdx P m` is the signing loop returning the selected nonce and index instead of the
signature; `Scheme.sign` is its image under encoding the revealed values.

The analysis of the loop, started from a cache `d`:

* `run_signIdx_extend`: cache entries of other lengths are irrelevant to the loop;
* `signIdx_support`: every new cache entry is an encoding entry at an input `m ++ η`; a new
  entry with a valid index is the one that ended the loop;
* `signIdx_bound`: with `IdxPre d u₁ i` the event that a pre-existing encoding entry `u ≠ u₁`
  has index `i`, the loop ends at a nonce `η` and index `i` with `IdxPre d (m ++ η) i` with
  probability at most `cntV d / numSets + trialLimit * pairs d / (2 ^ nonceBits - trialLimit)`.
  The statement is in the continuation form of the master lemma.
-/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal

noncomputable section

open scoped Classical

namespace OptimalOTS

/-! ## Lemmas shared with the lower-bound proof (copied: submissions may not import each other) -/

namespace Analysis

lemma setWidth_append_nonce {P : Params} (m : Message P) (η : Nonce P) :
    (m ++ η).setWidth P.nonceBits = η := by
  ext j hj
  simp [BitVec.getElem_setWidth, BitVec.getLsbD_append, hj]

lemma sum_fin_equivFin {α : Type*} {s : Finset α} {n : ℕ} (h : n = s.card) (G : α → ℝ≥0∞) :
    ∑ j : Fin n, G (s.equivFin.symm (Fin.cast h j)).1 = ∑ η ∈ s, G η := by
  rw [← Finset.sum_coe_sort s]
  exact Equiv.sum_comp ((finCongr h).trans s.equivFin.symm) (fun x => G x.1)

/-- The index read from an oracle output. -/
def idxOfOut (P : Params) (y : BitVec P.hashBits) : ℕ := (y.setWidth P.idxBits).toNat

/-- Number of oracle outputs whose index lies in a set of index values. -/
theorem card_idxOfOut_mem {P : Params} (hidx : P.idxBits ≤ P.hashBits) (A : Finset ℕ)
    (hA : ∀ n ∈ A, n < 2 ^ P.idxBits) :
    (Finset.univ.filter fun y : BitVec P.hashBits => idxOfOut P y ∈ A).card =
      A.card * 2 ^ (P.hashBits - P.idxBits) := by
  have hH : 2 ^ P.hashBits = 2 ^ P.idxBits * 2 ^ (P.hashBits - P.idxBits) := by
    rw [← pow_add, Nat.add_sub_cancel' hidx]
  have hNpos : 0 < 2 ^ P.idxBits := by positivity
  rw [← Finset.card_range (2 ^ (P.hashBits - P.idxBits)), ← Finset.card_product]
  refine Finset.card_nbij' (fun y => (y.toNat % 2 ^ P.idxBits, y.toNat / 2 ^ P.idxBits))
    (fun x => BitVec.ofNat P.hashBits (x.1 + 2 ^ P.idxBits * x.2)) ?_ ?_ ?_ ?_
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
    have h1 : x.1 + 2 ^ P.idxBits * x.2 < 2 ^ P.hashBits := by
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
    have h1 : x.1 + 2 ^ P.idxBits * x.2 < 2 ^ P.hashBits := by
      rw [hH]
      nlinarith
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt hx1, Nat.add_mul_div_left _ _ hNpos, Nat.div_eq_of_lt hx1, zero_add]

end Analysis


variable (P : Params)

/-- An encoding input. -/
abbrev EncInput (P : Params) := BitVec (P.msgBits + P.nonceBits)

/-- The encoding query at input `u`: the query of length `msgBits + nonceBits` with bits `u`. The
oracle has no labels, so an encoding query is told apart from every other query by its length. -/
def encQuery (u : EncInput P) : Query := ⟨P.msgBits + P.nonceBits, u⟩

/-- The index read from an oracle answer. -/
def idxOf (w : BitVec P.hashBits) : ℕ := (w.setWidth P.idxBits).toNat

/-- The signing loop, returning the nonce and the index. -/
def signIdxLoop (m : Message P) :
    ℕ → Finset (Nonce P) → OracleComp (Spec P) (Option (Nonce P × Fin P.numSets))
  | 0, _ => pure none
  | k + 1, tried =>
    let fresh := Finset.univ \ tried
    if h : 0 < fresh.card then do
      let j ← (liftM ($[0..(fresh.card - 1)]) : OracleComp (Spec P) (Fin (fresh.card - 1 + 1)))
      let η : Nonce P := (fresh.equivFin.symm (Fin.cast (by omega) j)).1
      let i ← index P m η
      if hi : i < P.numSets then
        return some (η, ⟨i, hi⟩)
      else
        signIdxLoop m k (insert η tried)
    else
      pure none

/-- Signing, returning the nonce and the index. -/
def signIdx (m : Message P) : OracleComp (Spec P) (Option (Nonce P × Fin P.numSets)) :=
  signIdxLoop P m P.trialLimit ∅

/-! ### Basic facts on encoding inputs -/

theorem encQuery_inj {u u' : EncInput P} (h : encQuery P u = encQuery P u') : u = u' := by
  simp only [encQuery, Sigma.mk.inj_iff, heq_eq_eq, true_and] at h
  exact h

/-- The length of an encoding query. -/
theorem encQuery_fst (u : EncInput P) : (encQuery P u).1 = P.msgBits + P.nonceBits := rfl

/-- A query of another length is not an encoding query. -/
theorem ne_encQuery_of_length_ne {q : Query} (hq : q.1 ≠ P.msgBits + P.nonceBits)
    (u : EncInput P) : q ≠ encQuery P u := by
  rintro rfl
  exact hq rfl

/-- The queries of encoding length are exactly the encoding queries. -/
theorem exists_eq_encQuery_of_length_eq {q : Query} (hq : q.1 = P.msgBits + P.nonceBits) :
    ∃ u : EncInput P, q = encQuery P u := by
  obtain ⟨k, v⟩ := q
  change k = P.msgBits + P.nonceBits at hq
  subst hq
  exact ⟨v, rfl⟩

theorem append_nonce_inj (m : Message P) {η η' : Nonce P} (h : m ++ η = m ++ η') : η = η' := by
  have := congrArg (fun u : EncInput P => u.setWidth P.nonceBits) h
  simpa only [Analysis.setWidth_append_nonce] using this

/-! ### The loop in query normal form -/

theorem liftM_uniformFin_eq (n : ℕ) :
    (liftM ($[0..n]) : OracleComp (Spec P) (Fin (n + 1))) =
      liftM ((Spec P).query (.inl n)) := by
  change liftComp ($[0..n]) (Spec P) = _
  simp [liftComp, ProbComp.uniformFin]
  rfl

/-- The continuation of the loop after the encoding answer `w` at nonce `η`. -/
def afterHash (m : Message P) (k : ℕ) (tried : Finset (Nonce P)) (η : Nonce P)
    (w : BitVec P.hashBits) : OracleComp (Spec P) (Option (Nonce P × Fin P.numSets)) :=
  if hi : idxOf P w < P.numSets then pure (some (η, ⟨idxOf P w, hi⟩))
  else signIdxLoop P m k (insert η tried)

/-- The body of the loop at nonce `η`: one encoding query, then stop or recurse. -/
def loopBody (m : Message P) (k : ℕ) (tried : Finset (Nonce P)) (η : Nonce P) :
    OracleComp (Spec P) (Option (Nonce P × Fin P.numSets)) :=
  (liftM ((Spec P).query (.inr (encQuery P (m ++ η)))) :
      OracleComp (Spec P) (BitVec P.hashBits)) >>= afterHash P m k tried η

/-- The nonce selected by the sample `j`. -/
def nonceOf (tried : Finset (Nonce P)) (hc : 0 < (Finset.univ \ tried).card)
    (j : Fin ((Finset.univ \ tried).card - 1 + 1)) : Nonce P :=
  ((Finset.univ \ tried).equivFin.symm (Fin.cast (by omega) j)).1

theorem nonceOf_mem (tried : Finset (Nonce P)) (hc : 0 < (Finset.univ \ tried).card)
    (j : Fin ((Finset.univ \ tried).card - 1 + 1)) :
    nonceOf P tried hc j ∈ Finset.univ \ tried :=
  ((Finset.univ \ tried).equivFin.symm (Fin.cast (by omega) j)).2

theorem signIdxLoop_succ (m : Message P) (k : ℕ) (tried : Finset (Nonce P))
    (hc : 0 < (Finset.univ \ tried).card) :
    signIdxLoop P m (k + 1) tried =
      (liftM ((Spec P).query (.inl ((Finset.univ \ tried).card - 1))) :
          OracleComp (Spec P) (Fin ((Finset.univ \ tried).card - 1 + 1))) >>= fun j =>
        loopBody P m k tried (nonceOf P tried hc j) := by
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

theorem signLoop_eq_map {P : Params} (S : Scheme P) (x : S.graph.Assignment) (m : Message P) :
    ∀ (k : ℕ) (tried : Finset (Nonce P)),
      S.signLoop x m k tried =
        (Option.map fun r : Nonce P × Fin P.numSets => (r.1, S.graph.encode (S.sets r.2) x)) <$>
          signIdxLoop P m k tried := by
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
theorem sign_eq_map {P : Params} (S : Scheme P) (x : S.graph.Assignment) (m : Message P) :
    S.sign x m =
      (Option.map fun r : Nonce P × Fin P.numSets => (r.1, S.graph.encode (S.sets r.2) x)) <$>
        signIdx P m :=
  signLoop_eq_map S x m P.trialLimit ∅

/-! ### Non-encoding entries are irrelevant -/

theorem run_signIdxLoop_extend (m : Message P) (f : Cache P)
    (hf : ∀ u : EncInput P, f (encQuery P u) = none) :
    ∀ (k : ℕ) (tried : Finset (Nonce P)) (d : Cache P),
      run P (signIdxLoop P m k tried) (Cache.extend d f) =
        (fun p => (p.1, Cache.extend p.2 f)) <$> run P (signIdxLoop P m k tried) d := by
  intro k
  induction k with
  | zero => intro tried d; simp [signIdxLoop, run_pure]
  | succ k ih =>
    intro tried d
    by_cases hc : 0 < (Finset.univ \ tried).card
    · rw [signIdxLoop_succ P m k tried hc, run_query_bind, run_query_bind, oracleImpl_run_inl,
        oracleImpl_run_inl]
      simp only [bind_assoc, pure_bind, map_bind]
      refine bind_congr fun j => ?_
      simp only [loopBody]
      rw [run_query_bind, run_query_bind]
      rcases hdq : d (encQuery P (m ++ nonceOf P tried hc j)) with _ | w
      · have hdq' : Cache.extend d f (encQuery P (m ++ nonceOf P tried hc j)) = none := by
          rw [Cache.extend_apply_of_none hdq]; exact hf _
        rw [oracleImpl_run_inr_none P hdq, oracleImpl_run_inr_none P hdq']
        simp only [bind_assoc, pure_bind, map_bind]
        refine bind_congr fun w => ?_
        rw [← Cache.extend_cacheQuery]
        simp only [afterHash]
        split_ifs with hi
        · simp [run_pure]
        · exact ih _ _
      · have hdq' : Cache.extend d f (encQuery P (m ++ nonceOf P tried hc j)) = some w :=
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
    (hf : ∀ u : EncInput P, f (encQuery P u) = none) :
    run P (signIdx P m) (Cache.extend d f) =
      (fun p => (p.1, Cache.extend p.2 f)) <$> run P (signIdx P m) d :=
  run_signIdxLoop_extend P m f hf P.trialLimit ∅ d

/-! ### The new cache entries -/

theorem signIdxLoop_support (m : Message P) :
    ∀ (k : ℕ) (tried : Finset (Nonce P)) (d : Cache P),
      ∀ p ∈ support (run P (signIdxLoop P m k tried) d),
        Cache.Sub d p.2 ∧
        (∀ q w, d q = none → p.2 q = some w →
          ∃ η : Nonce P, q = encQuery P (m ++ η) ∧
            ∀ hi : idxOf P w < P.numSets, p.1 = some (η, ⟨idxOf P w, hi⟩)) ∧
        (∀ η i, p.1 = some (η, i) →
          ∃ w, p.2 (encQuery P (m ++ η)) = some w ∧ idxOf P w = i.val) := by
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
    · rw [signIdxLoop_succ P m k tried hc] at hp
      obtain ⟨j, hp⟩ := mem_support_run_inl P hp
      simp only [loopBody] at hp
      generalize nonceOf P tried hc j = η at hp
      rcases hdq : d (encQuery P (m ++ η)) with _ | w
      · obtain ⟨w, hp⟩ := mem_support_run_inr_none P hdq hp
        rw [afterHash] at hp
        by_cases hi : idxOf P w < P.numSets
        · rw [dif_pos hi, run_pure, support_pure] at hp
          simp only [Set.mem_singleton_iff] at hp
          subst hp
          refine ⟨Cache.sub_cacheQuery_of_none hdq w, ?_, ?_⟩
          · intro q w' h1 h2
            change (d.cacheQuery (encQuery P (m ++ η)) w) q = some w' at h2
            by_cases hq : q = encQuery P (m ++ η)
            · subst hq
              rw [QueryCache.cacheQuery_self] at h2
              obtain rfl := Option.some.inj h2
              exact ⟨η, rfl, fun _ => rfl⟩
            · rw [QueryCache.cacheQuery_of_ne _ _ hq, h1] at h2
              cases h2
          · intro η' i h
            change some (η, ⟨idxOf P w, hi⟩) = some (η', i) at h
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            exact ⟨w, QueryCache.cacheQuery_self _ _ _, rfl⟩
        · rw [dif_neg hi] at hp
          obtain ⟨h1, h2, h3⟩ := ih (insert η tried) (d.cacheQuery _ w) p hp
          refine ⟨(Cache.sub_cacheQuery_of_none hdq w).trans h1, ?_, h3⟩
          intro q w' hq1 hq2
          by_cases hq : q = encQuery P (m ++ η)
          · subst hq
            have : p.2 (encQuery P (m ++ η)) = some w :=
              h1 _ _ (QueryCache.cacheQuery_self _ _ _)
            rw [this] at hq2
            obtain rfl := Option.some.inj hq2
            exact ⟨η, rfl, fun hi' => absurd hi' hi⟩
          · exact h2 q w' (by rw [QueryCache.cacheQuery_of_ne _ _ hq]; exact hq1) hq2
      · have hp := mem_support_run_inr_some P hdq hp
        rw [afterHash] at hp
        by_cases hi : idxOf P w < P.numSets
        · rw [dif_pos hi, run_pure, support_pure] at hp
          simp only [Set.mem_singleton_iff] at hp
          subst hp
          refine ⟨Cache.Sub.refl d, fun q w' h1 h2 => ?_, ?_⟩
          · change d q = some w' at h2
            rw [h1] at h2; cases h2
          · intro η' i h
            change some (η, ⟨idxOf P w, hi⟩) = some (η', i) at h
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
    ∀ p ∈ support (run P (signIdx P m) d),
      Cache.Sub d p.2 ∧
      (∀ q w, d q = none → p.2 q = some w →
        ∃ η : Nonce P, q = encQuery P (m ++ η) ∧
          ∀ hi : idxOf P w < P.numSets, p.1 = some (η, ⟨idxOf P w, hi⟩)) ∧
      (∀ η i, p.1 = some (η, i) → ∃ w, p.2 (encQuery P (m ++ η)) = some w ∧ idxOf P w = i.val) :=
  signIdxLoop_support P m P.trialLimit ∅ d

/-! ### The signing bound -/

/-- A pre-existing encoding entry other than `u₁` has index `i`. -/
def IdxPre (d : Cache P) (u₁ : EncInput P) (i : ℕ) : Prop :=
  ∃ u, u ≠ u₁ ∧ ∃ w, d (encQuery P u) = some w ∧ idxOf P w = i

/-- Number of encoding entries with a valid index. -/
def cntV (d : Cache P) : ℕ :=
  (Finset.univ.filter fun u : EncInput P =>
    ∃ w, d (encQuery P u) = some w ∧ idxOf P w < P.numSets).card

/-- Number of ordered pairs of distinct encoding entries with equal indices. -/
def pairs (d : Cache P) : ℕ :=
  ((Finset.univ ×ˢ Finset.univ).filter fun p : EncInput P × EncInput P =>
    p.1 ≠ p.2 ∧ ∃ w w', d (encQuery P p.1) = some w ∧ d (encQuery P p.2) = some w' ∧
      idxOf P w = idxOf P w').card

/-- `Φ` does not see encoding entries: the entries at queries of length `msgBits + nonceBits`. -/
def EncInvariant (Φ : Cache P → ℝ≥0∞) : Prop :=
  ∀ (c : Cache P) (u : EncInput P) (w : BitVec P.hashBits),
    Φ (c.cacheQuery (encQuery P u) w) = Φ c

/-- `d'` extends `d` by the entries of a signing run with outcome `r`. -/
def SignExt (m : Message P) (d : Cache P) (r : Option (Nonce P × Fin P.numSets)) (d' : Cache P) :
    Prop :=
  Cache.Sub d d' ∧
  (∀ q w, d q = none → d' q = some w →
    ∃ η : Nonce P, q = encQuery P (m ++ η) ∧
      ∀ hi : idxOf P w < P.numSets, r = some (η, ⟨idxOf P w, hi⟩)) ∧
  (∀ η i, r = some (η, i) → ∃ w, d' (encQuery P (m ++ η)) = some w ∧ idxOf P w = i.val)

/-- The set of ordered pairs counted by `pairs`. -/
def pairSet (d : Cache P) : Finset (EncInput P × EncInput P) :=
  (Finset.univ ×ˢ Finset.univ).filter fun p : EncInput P × EncInput P =>
    p.1 ≠ p.2 ∧ ∃ w w', d (encQuery P p.1) = some w ∧ d (encQuery P p.2) = some w' ∧
      idxOf P w = idxOf P w'

/-- Inputs of `d` whose index is shared with another entry. -/
def W (d : Cache P) : Finset (EncInput P) := (pairSet P d).image Prod.fst

theorem card_W_le (d : Cache P) : (W P d).card ≤ pairs P d := Finset.card_image_le

theorem mem_W {d : Cache P} {u : EncInput P} {w : BitVec P.hashBits}
    (hu : d (encQuery P u) = some w) (h : IdxPre P d u (idxOf P w)) : u ∈ W P d := by
  obtain ⟨u', hne, w', hu', hw'⟩ := h
  refine Finset.mem_image.2 ⟨(u, u'), ?_, rfl⟩
  simp only [pairSet, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and]
  exact ⟨hne.symm, w, w', hu, hu', hw'.symm⟩

/-- The set counted by `cntV`. -/
def validSet (d : Cache P) : Finset (EncInput P) :=
  Finset.univ.filter fun u : EncInput P => ∃ w, d (encQuery P u) = some w ∧ idxOf P w < P.numSets

/-- The valid indices of the entries of `d`. -/
def V (d : Cache P) : Finset ℕ :=
  (validSet P d).image fun u => ((d (encQuery P u)).map (idxOf P)).getD 0

theorem card_V_le (d : Cache P) : (V P d).card ≤ cntV P d := Finset.card_image_le

theorem mem_V {d : Cache P} {u : EncInput P} {w : BitVec P.hashBits}
    (hu : d (encQuery P u) = some w) (hw : idxOf P w < P.numSets) : idxOf P w ∈ V P d := by
  refine Finset.mem_image.2 ⟨u, ?_, ?_⟩
  · simp only [validSet, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨w, hu, hw⟩
  · simp [hu]

theorem V_lt (d : Cache P) : ∀ n ∈ V P d, n < 2 ^ P.idxBits := by
  intro n hn
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hn
  simp only [validSet, Finset.mem_filter, Finset.mem_univ, true_and] at hu
  obtain ⟨w, hw, -⟩ := hu
  simp only [hw, Option.map_some, Option.getD_some]
  exact (w.setWidth P.idxBits).isLt

theorem card_idxOf_mem (hidx : P.idxBits ≤ P.hashBits) (A : Finset ℕ)
    (hA : ∀ n ∈ A, n < 2 ^ P.idxBits) :
    (Finset.univ.filter fun y : BitVec P.hashBits => idxOf P y ∈ A).card =
      A.card * 2 ^ (P.hashBits - P.idxBits) :=
  Analysis.card_idxOfOut_mem hidx A hA

theorem E_query_unif (n : ℕ) (g : Fin (n + 1) → ℝ≥0∞) :
    E (HasQuery.query (spec := unifSpec) (m := ProbComp) n) g =
      ∑ j, ((n : ℝ≥0∞) + 1)⁻¹ * g j := by
  rw [E, expectedValue_def, tsum_fintype]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  exact ProbComp.probOutput_uniformFin n j

theorem cache_eq_of_notMem {d d' : Cache P} {m : Message P} {tried : Finset (Nonce P)}
    (hSub : Cache.Sub d d')
    (hNew : ∀ q w, d q = none → d' q = some w →
      ∃ η ∈ tried, q = encQuery P (m ++ η) ∧ ¬ idxOf P w < P.numSets)
    {η : Nonce P} (hη : η ∉ tried) :
    d' (encQuery P (m ++ η)) = d (encQuery P (m ++ η)) := by
  rcases hdq : d (encQuery P (m ++ η)) with _ | w
  · rcases hd'q : d' (encQuery P (m ++ η)) with _ | w'
    · rfl
    · obtain ⟨η', hη', he, -⟩ := hNew _ _ hdq hd'q
      exact absurd (by rw [append_nonce_inj P m (encQuery_inj P he)]; exact hη') hη
  · exact hSub _ _ hdq

theorem new_cacheQuery {d d' : Cache P} {m : Message P} {tried : Finset (Nonce P)}
    (hNew : ∀ q w, d q = none → d' q = some w →
      ∃ η ∈ tried, q = encQuery P (m ++ η) ∧ ¬ idxOf P w < P.numSets)
    (η : Nonce P) {w : BitVec P.hashBits} (hw : ¬ idxOf P w < P.numSets) :
    ∀ q w', d q = none → (d'.cacheQuery (encQuery P (m ++ η)) w) q = some w' →
      ∃ η' ∈ insert η tried, q = encQuery P (m ++ η') ∧ ¬ idxOf P w' < P.numSets := by
  intro q w' h1 h2
  by_cases hq : q = encQuery P (m ++ η)
  · subst hq
    rw [QueryCache.cacheQuery_self] at h2
    obtain rfl := Option.some.inj h2
    exact ⟨η, Finset.mem_insert_self _ _, rfl, hw⟩
  · rw [QueryCache.cacheQuery_of_ne _ _ hq] at h2
    obtain ⟨η', hη', he, hi⟩ := hNew q w' h1 h2
    exact ⟨η', Finset.mem_insert_of_mem hη', he, hi⟩

theorem new_insert {d d' : Cache P} {m : Message P} {tried : Finset (Nonce P)}
    (hNew : ∀ q w, d q = none → d' q = some w →
      ∃ η ∈ tried, q = encQuery P (m ++ η) ∧ ¬ idxOf P w < P.numSets)
    (η : Nonce P) :
    ∀ q w, d q = none → d' q = some w →
      ∃ η' ∈ insert η tried, q = encQuery P (m ++ η') ∧ ¬ idxOf P w < P.numSets :=
  fun q w h1 h2 =>
    let ⟨η', hη', he, hi⟩ := hNew q w h1 h2
    ⟨η', Finset.mem_insert_of_mem hη', he, hi⟩

theorem signExt_none {d d' : Cache P} {m : Message P} {tried : Finset (Nonce P)}
    (hSub : Cache.Sub d d')
    (hNew : ∀ q w, d q = none → d' q = some w →
      ∃ η ∈ tried, q = encQuery P (m ++ η) ∧ ¬ idxOf P w < P.numSets) :
    SignExt P m d none d' := by
  unfold SignExt
  refine ⟨hSub, fun q w h1 h2 => ?_, fun η i h => by cases h⟩
  obtain ⟨η, -, he, hi⟩ := hNew q w h1 h2
  exact ⟨η, he, fun hi' => absurd hi' hi⟩

theorem signExt_cached {d d' : Cache P} {m : Message P} {tried : Finset (Nonce P)}
    (hSub : Cache.Sub d d')
    (hNew : ∀ q w, d q = none → d' q = some w →
      ∃ η ∈ tried, q = encQuery P (m ++ η) ∧ ¬ idxOf P w < P.numSets)
    {η : Nonce P} {w : BitVec P.hashBits} (hi : idxOf P w < P.numSets)
    (hq : d' (encQuery P (m ++ η)) = some w) :
    SignExt P m d (some (η, ⟨idxOf P w, hi⟩)) d' := by
  unfold SignExt
  refine ⟨hSub, fun q w' h1 h2 => ?_, fun η' i h => ?_⟩
  · obtain ⟨η', -, he, hi'⟩ := hNew q w' h1 h2
    exact ⟨η', he, fun h => absurd h hi'⟩
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨w, hq, rfl⟩

theorem signExt_fresh {d d' : Cache P} {m : Message P} {tried : Finset (Nonce P)}
    (hSub : Cache.Sub d d')
    (hNew : ∀ q w, d q = none → d' q = some w →
      ∃ η ∈ tried, q = encQuery P (m ++ η) ∧ ¬ idxOf P w < P.numSets)
    {η : Nonce P} {w : BitVec P.hashBits} (hi : idxOf P w < P.numSets)
    (hq : d' (encQuery P (m ++ η)) = none) :
    SignExt P m d (some (η, ⟨idxOf P w, hi⟩)) (d'.cacheQuery (encQuery P (m ++ η)) w) := by
  unfold SignExt
  refine ⟨hSub.trans (Cache.sub_cacheQuery_of_none hq w), fun q w' h1 h2 => ?_,
    fun η' i h => ?_⟩
  · by_cases hqe : q = encQuery P (m ++ η)
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

theorem ind_le_V {d : Cache P} {m : Message P} {η : Nonce P} {w : BitVec P.hashBits}
    (hi : idxOf P w < P.numSets) :
    (if ∃ η' i, (some (η, ⟨idxOf P w, hi⟩) : Option (Nonce P × Fin P.numSets)) = some (η', i) ∧
        IdxPre P d (m ++ η') i.val then (1 : ℝ≥0∞) else 0) ≤
      if idxOf P w ∈ V P d then 1 else 0 := by
  by_cases h1 : ∃ η' i, (some (η, ⟨idxOf P w, hi⟩) : Option (Nonce P × Fin P.numSets)) =
      some (η', i) ∧ IdxPre P d (m ++ η') i.val
  · rw [if_pos h1]
    obtain ⟨η', i, he, hpre⟩ := h1
    simp only [Option.some.injEq, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    obtain ⟨u, -, w', hu, hw'⟩ := hpre
    have hw'' : idxOf P w' = idxOf P w := hw'
    have := mem_V P hu (by rw [hw'']; exact hi)
    rw [hw''] at this
    rw [if_pos this]
  · rw [if_neg h1]; exact zero_le

theorem ind_le_W {d : Cache P} {m : Message P} {η : Nonce P} {w : BitVec P.hashBits}
    (hi : idxOf P w < P.numSets) (hw : d (encQuery P (m ++ η)) = some w) :
    (if ∃ η' i, (some (η, ⟨idxOf P w, hi⟩) : Option (Nonce P × Fin P.numSets)) = some (η', i) ∧
        IdxPre P d (m ++ η') i.val then (1 : ℝ≥0∞) else 0) ≤
      if m ++ η ∈ W P d then 1 else 0 := by
  by_cases h1 : ∃ η' i, (some (η, ⟨idxOf P w, hi⟩) : Option (Nonce P × Fin P.numSets)) =
      some (η', i) ∧ IdxPre P d (m ++ η') i.val
  · rw [if_pos h1]
    obtain ⟨η', i, he, hpre⟩ := h1
    simp only [Option.some.injEq, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    rw [if_pos (mem_W P hw hpre)]
  · rw [if_neg h1]; exact zero_le

theorem sum_inv_card_split {n : ℕ} (X : ℝ≥0∞) (Y Z : BitVec n → ℝ≥0∞) :
    ∑ w, (Fintype.card (BitVec n) : ℝ≥0∞)⁻¹ * (X + Y w + Z w) =
      X + (Fintype.card (BitVec n) : ℝ≥0∞)⁻¹ * ∑ w, Y w +
        (Fintype.card (BitVec n) : ℝ≥0∞)⁻¹ * ∑ w, Z w := by
  simp only [mul_add, Finset.sum_add_distrib, sum_inv_card_mul, Finset.mul_sum]

theorem not_exists_none {d : Cache P} {m : Message P} :
    ¬ ∃ (η : Nonce P) (i : Fin P.numSets),
      (none : Option (Nonce P × Fin P.numSets)) = some (η, i) ∧ IdxPre P d (m ++ η) i.val := by
  rintro ⟨_, _, h, _⟩
  cases h

/-- The generalized signing bound: `k` further trials, nonces `tried` already used, current
cache `d'` differing from `d` only by encoding entries at tried nonces. -/
theorem signIdxLoop_bound (hM : 0 < P.numSets) (hM' : P.numSets ≤ 2 ^ P.idxBits)
    (hidx : P.idxBits ≤ P.hashBits) (hL : P.trialLimit < 2 ^ P.nonceBits)
    (m : Message P) (d : Cache P) {β J : Type} [Nonempty J]
    (kont : J → Option (Nonce P × Fin P.numSets) → OracleComp (Spec P) β)
    (F : Option (Nonce P × Fin P.numSets) → Cache P → ℝ≥0∞)
    (Φ : Cache P → ℝ≥0∞) (hΦ : EncInvariant P Φ) (κ lam : ℝ≥0∞)
    (I : Cache P → ℕ → Prop)
    (hI_fresh : ∀ c b q, I c b → c q = none → queryCost P (.inr q) ≤ b →
      ∀ u, I (c.cacheQuery q u) (b - queryCost P (.inr q)))
    (hI_cached : ∀ c b q, I c b → (c q).isSome → queryCost P (.inr q) ≤ b →
      I c (b - queryCost P (.inr q)))
    (hF : ∀ r d' b', SignExt P m d r d' → I d' b' → (∀ j, CostAtMost P (kont j r) b') →
      F r d' ≤ Φ d' + lam * (if ∃ η i, r = some (η, i) ∧ IdxPre P d (m ++ η) i.val then 1 else 0) +
        κ * b') :
    ∀ (k : ℕ) (tried : Finset (Nonce P)) (d' : Cache P) (b : ℕ),
      Cache.Sub d d' →
      (∀ q w, d q = none → d' q = some w →
        ∃ η ∈ tried, q = encQuery P (m ++ η) ∧ ¬ idxOf P w < P.numSets) →
      Φ d' = Φ d →
      tried.card + k ≤ P.trialLimit →
      I d' b →
      (∀ j, CostAtMost P (signIdxLoop P m k tried >>= kont j) b) →
      E (run P (signIdxLoop P m k tried) d') (fun p => F p.1 p.2) ≤
        Φ d + lam * ((P.numSets : ℝ≥0∞)⁻¹ * cntV P d +
          (k : ℝ≥0∞) * (((2 ^ P.nonceBits - P.trialLimit : ℕ) : ℝ≥0∞)⁻¹ * pairs P d)) +
          κ * b := by
  intro k
  induction k with
  | zero =>
    intro tried d' b hSub hNew hΦd hcard hI hB
    rw [signIdxLoop, run_pure, E_pure]
    simp only [signIdxLoop, pure_bind] at hB
    refine (hF none d' b (signExt_none P hSub hNew) hI hB).trans ?_
    rw [hΦd, if_neg (not_exists_none P), mul_zero, add_zero]
    simp only [Nat.cast_zero, zero_mul, add_zero]
    exact add_le_add_left le_self_add _
  | succ k ih =>
    intro tried d' b hSub hNew hΦd hcard hI hB
    by_cases hc : 0 < (Finset.univ \ tried).card
    · simp only [signIdxLoop_succ P m k tried hc] at hB ⊢
      have hB' : ∀ j i, CostAtMost P (loopBody P m k tried (nonceOf P tried hc i) >>= kont j) b :=
        fun j => costAtMost_inl_bind P _ _ _ (hB j)
      rw [run_query_bind, E_bind, oracleImpl_run_inl, E_bind, E_query_unif]
      simp only [E_pure]
      have hcast : (Finset.univ \ tried).card - 1 + 1 = (Finset.univ \ tried).card := by omega
      have hcR : (((Finset.univ \ tried).card - 1 : ℕ) : ℝ≥0∞) + 1 =
          ((Finset.univ \ tried).card : ℝ≥0∞) := by
        rw [← Nat.cast_add_one, hcast]
      simp only [hcR]
      have hc0 : ((Finset.univ \ tried).card : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.2 hc.ne'
      have hct : ((Finset.univ \ tried).card : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
      have hM0 : (P.numSets : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.2 hM.ne'
      have hMt : (P.numSets : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
      have hH0 : (Fintype.card (BitVec P.hashBits) : ℝ≥0∞) ≠ 0 :=
        Nat.cast_ne_zero.2 Fintype.card_ne_zero
      have hHt : (Fintype.card (BitVec P.hashBits) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
      set C : ℝ≥0∞ := lam * ((P.numSets : ℝ≥0∞)⁻¹ * cntV P d +
        (k : ℝ≥0∞) * (((2 ^ P.nonceBits - P.trialLimit : ℕ) : ℝ≥0∞)⁻¹ * pairs P d)) with hC
      -- counting facts
      have hY : (∑ w : BitVec P.hashBits, lam * (if idxOf P w ∈ V P d then (1 : ℝ≥0∞) else 0)) ≤
          lam * ((cntV P d : ℝ≥0∞) * (2 ^ (P.hashBits - P.idxBits) : ℕ)) := by
        rw [← Finset.mul_sum, Finset.sum_boole, card_idxOf_mem P hidx _ (V_lt P d), ← Nat.cast_mul]
        exact mul_le_mul_right (Nat.cast_le.2 (Nat.mul_le_mul_right _ (card_V_le P d))) _
      have hval : (∑ w : BitVec P.hashBits, if idxOf P w < P.numSets then (1 : ℝ≥0∞) else 0) =
          (P.numSets : ℝ≥0∞) * (2 ^ (P.hashBits - P.idxBits) : ℕ) := by
        rw [Finset.sum_boole]
        have h1 : (Finset.univ.filter fun w : BitVec P.hashBits => idxOf P w < P.numSets) =
            Finset.univ.filter fun w : BitVec P.hashBits => idxOf P w ∈ Finset.range P.numSets := by
          ext w; simp
        rw [h1, card_idxOf_mem P hidx _ (fun n hn => lt_of_lt_of_le (Finset.mem_range.1 hn) hM'),
          Finset.card_range, Nat.cast_mul]
      have hsplit : (∑ w : BitVec P.hashBits, if idxOf P w < P.numSets then (1 : ℝ≥0∞) else 0) +
          (∑ w : BitVec P.hashBits, if idxOf P w < P.numSets then (0 : ℝ≥0∞) else 1) =
          (Fintype.card (BitVec P.hashBits) : ℝ≥0∞) := by
        rw [← Finset.sum_add_distrib]
        have h1 : ∀ w : BitVec P.hashBits,
            ((if idxOf P w < P.numSets then (1 : ℝ≥0∞) else 0) +
              (if idxOf P w < P.numSets then (0 : ℝ≥0∞) else 1)) = 1 := by
          intro w; split_ifs <;> simp
        simp only [h1, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
      have hZ : (∑ w : BitVec P.hashBits, if idxOf P w < P.numSets then (0 : ℝ≥0∞) else C) =
          (∑ w : BitVec P.hashBits, if idxOf P w < P.numSets then (0 : ℝ≥0∞) else 1) * C := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun w _ => by split_ifs <;> simp
      have hcQ : (cntV P d : ℝ≥0∞) * (2 ^ (P.hashBits - P.idxBits) : ℕ) =
          ((P.numSets : ℝ≥0∞)⁻¹ * cntV P d) *
            ((P.numSets : ℝ≥0∞) * (2 ^ (P.hashBits - P.idxBits) : ℕ)) := by
        calc (cntV P d : ℝ≥0∞) * (2 ^ (P.hashBits - P.idxBits) : ℕ)
            = ((P.numSets : ℝ≥0∞)⁻¹ * P.numSets) *
                ((cntV P d : ℝ≥0∞) * (2 ^ (P.hashBits - P.idxBits) : ℕ)) := by
              rw [ENNReal.inv_mul_cancel hM0 hMt, one_mul]
          _ = _ := by ring
      have hCV : lam * ((cntV P d : ℝ≥0∞) * (2 ^ (P.hashBits - P.idxBits) : ℕ)) ≤
          C * (∑ w : BitVec P.hashBits, if idxOf P w < P.numSets then (1 : ℝ≥0∞) else 0) := by
        rw [hval, hcQ, hC]
        calc lam * ((P.numSets : ℝ≥0∞)⁻¹ * cntV P d *
                ((P.numSets : ℝ≥0∞) * (2 ^ (P.hashBits - P.idxBits) : ℕ)))
            ≤ lam * (((P.numSets : ℝ≥0∞)⁻¹ * cntV P d +
                (k : ℝ≥0∞) * (((2 ^ P.nonceBits - P.trialLimit : ℕ) : ℝ≥0∞)⁻¹ * pairs P d)) *
                ((P.numSets : ℝ≥0∞) * (2 ^ (P.hashBits - P.idxBits) : ℕ))) :=
              mul_le_mul_right (mul_le_mul_left le_self_add _) _
          _ = _ := by ring
      have hkey : (Fintype.card (BitVec P.hashBits) : ℝ≥0∞)⁻¹ *
            (∑ w : BitVec P.hashBits, lam * (if idxOf P w ∈ V P d then (1 : ℝ≥0∞) else 0)) +
          (Fintype.card (BitVec P.hashBits) : ℝ≥0∞)⁻¹ *
            (∑ w : BitVec P.hashBits, if idxOf P w < P.numSets then (0 : ℝ≥0∞) else C) ≤ C := by
        calc (Fintype.card (BitVec P.hashBits) : ℝ≥0∞)⁻¹ *
                (∑ w : BitVec P.hashBits, lam * (if idxOf P w ∈ V P d then (1 : ℝ≥0∞) else 0)) +
              (Fintype.card (BitVec P.hashBits) : ℝ≥0∞)⁻¹ *
                (∑ w : BitVec P.hashBits, if idxOf P w < P.numSets then (0 : ℝ≥0∞) else C)
            ≤ (Fintype.card (BitVec P.hashBits) : ℝ≥0∞)⁻¹ *
                (C * ∑ w : BitVec P.hashBits, if idxOf P w < P.numSets then (1 : ℝ≥0∞) else 0) +
              (Fintype.card (BitVec P.hashBits) : ℝ≥0∞)⁻¹ *
                (C * ∑ w : BitVec P.hashBits, if idxOf P w < P.numSets then (0 : ℝ≥0∞) else 1) :=
              add_le_add (mul_le_mul_right (hY.trans hCV) _) (le_of_eq (by rw [hZ]; ring))
          _ = (Fintype.card (BitVec P.hashBits) : ℝ≥0∞)⁻¹ * (C *
                ((∑ w : BitVec P.hashBits, if idxOf P w < P.numSets then (1 : ℝ≥0∞) else 0) +
                (∑ w : BitVec P.hashBits, if idxOf P w < P.numSets then (0 : ℝ≥0∞) else 1))) := by
              ring
          _ = (Fintype.card (BitVec P.hashBits) : ℝ≥0∞)⁻¹ *
                (C * (Fintype.card (BitVec P.hashBits) : ℝ≥0∞)) := by rw [hsplit]
          _ = C := by rw [mul_comm C, ← mul_assoc, ENNReal.inv_mul_cancel hH0 hHt, one_mul]
      -- the per-nonce bound
      have per : ∀ η ∈ Finset.univ \ tried,
          (∀ j, CostAtMost P (loopBody P m k tried η >>= kont j) b) →
          E (run P (loopBody P m k tried η) d') (fun p => F p.1 p.2) ≤
            (Φ d + κ * b + C) + lam * (if m ++ η ∈ W P d then 1 else 0) := by
        intro η hη hBη
        have hηt : η ∉ tried := (Finset.mem_sdiff.1 hη).2
        have hins : (insert η tried).card + k ≤ P.trialLimit := by
          rw [Finset.card_insert_of_notMem hηt]; omega
        have hBw : ∀ j w, CostAtMost P (afterHash P m k tried η w >>= kont j)
            (b - queryCost P (.inr (encQuery P (m ++ η)))) :=
          fun j => (costAtMost_inr_bind P _ _ _ (hBη j)).2
        have hcost : queryCost P (.inr (encQuery P (m ++ η))) ≤ b :=
          (costAtMost_inr_bind P _ _ _ (hBη (Classical.arbitrary J))).1
        have hb₁ : ((b - queryCost P (.inr (encQuery P (m ++ η))) : ℕ) : ℝ≥0∞) ≤ b :=
          Nat.cast_le.2 (Nat.sub_le _ _)
        have hq : d' (encQuery P (m ++ η)) = d (encQuery P (m ++ η)) :=
          cache_eq_of_notMem P hSub hNew hηt
        simp only [loopBody]
        rw [run_query_bind, E_bind]
        rcases hdq : d (encQuery P (m ++ η)) with _ | w
        · -- fresh encoding query
          rw [hdq] at hq
          rw [oracleImpl_run_inr_none P hq, E_bind, E_uniform]
          simp only [E_pure]
          have hΦ' : ∀ w, Φ (d'.cacheQuery (encQuery P (m ++ η)) w) = Φ d := fun w =>
            (hΦ d' (m ++ η) w).trans hΦd
          have hSub' : ∀ w, Cache.Sub d (d'.cacheQuery (encQuery P (m ++ η)) w) := fun w =>
            hSub.trans (Cache.sub_cacheQuery_of_none hq w)
          have perw : ∀ w : BitVec P.hashBits,
              E (run P (afterHash P m k tried η w) (d'.cacheQuery (encQuery P (m ++ η)) w))
                (fun p => F p.1 p.2) ≤
              Φ d + κ * b + lam * (if idxOf P w ∈ V P d then 1 else 0) +
                (if idxOf P w < P.numSets then 0 else C) := by
            intro w
            by_cases hi : idxOf P w < P.numSets
            · rw [afterHash, dif_pos hi, run_pure, E_pure, if_pos hi, add_zero]
              have hBk : ∀ j, CostAtMost P (kont j (some (η, ⟨idxOf P w, hi⟩)))
                  (b - queryCost P (.inr (encQuery P (m ++ η)))) := fun j => by
                have := hBw j w
                rwa [afterHash, dif_pos hi, pure_bind] at this
              refine (hF _ _ _ (signExt_fresh P hSub hNew hi hq)
                (hI_fresh d' b _ hI hq hcost w) hBk).trans ?_
              rw [hΦ' w]
              calc _ ≤ Φ d + lam * (if idxOf P w ∈ V P d then 1 else 0) + κ * b :=
                    add_le_add (add_le_add_right (mul_le_mul_right (ind_le_V P hi) _) _)
                      (mul_le_mul_right hb₁ _)
                _ = Φ d + κ * b + lam * (if idxOf P w ∈ V P d then 1 else 0) := by ring
            · rw [afterHash, dif_neg hi, if_neg hi]
              have hBk : ∀ j, CostAtMost P (signIdxLoop P m k (insert η tried) >>= kont j)
                  (b - queryCost P (.inr (encQuery P (m ++ η)))) := fun j => by
                have := hBw j w
                rwa [afterHash, dif_neg hi] at this
              refine (ih (insert η tried) _ _ (hSub' w) (new_cacheQuery P hNew η hi) (hΦ' w)
                hins (hI_fresh d' b _ hI hq hcost w) hBk).trans ?_
              calc _ ≤ Φ d + lam * ((P.numSets : ℝ≥0∞)⁻¹ * cntV P d +
                    (k : ℝ≥0∞) * (((2 ^ P.nonceBits - P.trialLimit : ℕ) : ℝ≥0∞)⁻¹ * pairs P d)) +
                    κ * b := add_le_add_right (mul_le_mul_right hb₁ _) _
                _ = Φ d + κ * b + C := by rw [hC]; ring
                _ ≤ Φ d + κ * b + lam * (if idxOf P w ∈ V P d then 1 else 0) + C :=
                    add_le_add_left le_self_add _
          calc _ ≤ ∑ w : BitVec P.hashBits, (Fintype.card (BitVec P.hashBits) : ℝ≥0∞)⁻¹ *
                (Φ d + κ * b + lam * (if idxOf P w ∈ V P d then 1 else 0) +
                  (if idxOf P w < P.numSets then 0 else C)) :=
                Finset.sum_le_sum fun w _ => mul_le_mul_right (perw w) _
            _ = Φ d + κ * b + (Fintype.card (BitVec P.hashBits) : ℝ≥0∞)⁻¹ *
                  (∑ w : BitVec P.hashBits, lam * (if idxOf P w ∈ V P d then (1 : ℝ≥0∞) else 0)) +
                (Fintype.card (BitVec P.hashBits) : ℝ≥0∞)⁻¹ *
                  (∑ w : BitVec P.hashBits, if idxOf P w < P.numSets then (0 : ℝ≥0∞) else C) :=
                sum_inv_card_split _ _ _
            _ = Φ d + κ * b + ((Fintype.card (BitVec P.hashBits) : ℝ≥0∞)⁻¹ *
                  (∑ w : BitVec P.hashBits, lam * (if idxOf P w ∈ V P d then (1 : ℝ≥0∞) else 0)) +
                (Fintype.card (BitVec P.hashBits) : ℝ≥0∞)⁻¹ *
                  (∑ w : BitVec P.hashBits, if idxOf P w < P.numSets then (0 : ℝ≥0∞) else C)) := by
                rw [add_assoc]
            _ ≤ Φ d + κ * b + C := add_le_add_right hkey _
            _ ≤ (Φ d + κ * b + C) + lam * (if m ++ η ∈ W P d then 1 else 0) := le_self_add
        · -- cached encoding query
          rw [hdq] at hq
          rw [oracleImpl_run_inr_some P hq, E_pure]
          by_cases hi : idxOf P w < P.numSets
          · rw [afterHash, dif_pos hi, run_pure, E_pure]
            have hBk : ∀ j, CostAtMost P (kont j (some (η, ⟨idxOf P w, hi⟩)))
                (b - queryCost P (.inr (encQuery P (m ++ η)))) := fun j => by
              have := hBw j w
              rwa [afterHash, dif_pos hi, pure_bind] at this
            refine (hF _ _ _ (signExt_cached P hSub hNew hi hq)
              (hI_cached d' b _ hI (by simp [hq]) hcost) hBk).trans ?_
            rw [hΦd]
            calc _ ≤ Φ d + lam * (if m ++ η ∈ W P d then 1 else 0) + κ * b :=
                  add_le_add (add_le_add_right (mul_le_mul_right (ind_le_W P hi hdq) _) _)
                    (mul_le_mul_right hb₁ _)
              _ = Φ d + κ * b + lam * (if m ++ η ∈ W P d then 1 else 0) := by ring
              _ ≤ (Φ d + κ * b + C) + lam * (if m ++ η ∈ W P d then 1 else 0) :=
                  add_le_add_left le_self_add _
          · rw [afterHash, dif_neg hi]
            have hBk : ∀ j, CostAtMost P (signIdxLoop P m k (insert η tried) >>= kont j)
                (b - queryCost P (.inr (encQuery P (m ++ η)))) := fun j => by
              have := hBw j w
              rwa [afterHash, dif_neg hi] at this
            refine (ih (insert η tried) d' _ hSub (new_insert P hNew η) hΦd hins
              (hI_cached d' b _ hI (by simp [hq]) hcost) hBk).trans ?_
            calc _ ≤ Φ d + lam * ((P.numSets : ℝ≥0∞)⁻¹ * cntV P d +
                  (k : ℝ≥0∞) * (((2 ^ P.nonceBits - P.trialLimit : ℕ) : ℝ≥0∞)⁻¹ * pairs P d)) +
                  κ * b := add_le_add_right (mul_le_mul_right hb₁ _) _
              _ = Φ d + κ * b + C := by rw [hC]; ring
              _ ≤ (Φ d + κ * b + C) + lam * (if m ++ η ∈ W P d then 1 else 0) := le_self_add
      -- average over the nonce
      have hsum : (∑ η ∈ Finset.univ \ tried, if m ++ η ∈ W P d then (1 : ℝ≥0∞) else 0) ≤
          pairs P d := by
        rw [Finset.sum_boole]
        refine Nat.cast_le.2 ((Finset.card_le_card_of_injOn (fun η => m ++ η) ?_ ?_).trans
          (card_W_le P d))
        · intro η hη
          rw [Finset.mem_coe, Finset.mem_filter] at hη
          exact hη.2
        · intro η _ η' _ h
          exact append_nonce_inj P m h
      have hDc : ((2 ^ P.nonceBits - P.trialLimit : ℕ) : ℝ≥0∞) ≤
          ((Finset.univ \ tried).card : ℝ≥0∞) := by
        refine Nat.cast_le.2 ?_
        rw [Finset.card_univ_sdiff, Fintype.card_bitVec]
        omega
      have hstep1 : ∀ j : Fin ((Finset.univ \ tried).card - 1 + 1),
          ((Finset.univ \ tried).card : ℝ≥0∞)⁻¹ *
            E (run P (loopBody P m k tried (nonceOf P tried hc j)) d') (fun p => F p.1 p.2) ≤
          ((Finset.univ \ tried).card : ℝ≥0∞)⁻¹ *
            ((Φ d + κ * b + C) + lam * (if m ++ nonceOf P tried hc j ∈ W P d then 1 else 0)) :=
        fun j => mul_le_mul_right (per _ (nonceOf_mem P tried hc j) (fun i => hB' i j)) _
      have hstep2 := Analysis.sum_fin_equivFin hcast fun η =>
        ((Finset.univ \ tried).card : ℝ≥0∞)⁻¹ *
          ((Φ d + κ * b + C) + lam * (if m ++ η ∈ W P d then 1 else 0))
      calc ∑ j, ((Finset.univ \ tried).card : ℝ≥0∞)⁻¹ *
            E (run P (loopBody P m k tried (nonceOf P tried hc j)) d') (fun p => F p.1 p.2)
          ≤ ∑ j, ((Finset.univ \ tried).card : ℝ≥0∞)⁻¹ *
              ((Φ d + κ * b + C) + lam * (if m ++ nonceOf P tried hc j ∈ W P d then 1 else 0)) :=
            Finset.sum_le_sum fun j _ => hstep1 j
        _ = ∑ η ∈ Finset.univ \ tried, ((Finset.univ \ tried).card : ℝ≥0∞)⁻¹ *
              ((Φ d + κ * b + C) + lam * (if m ++ η ∈ W P d then 1 else 0)) := hstep2
        _ = (Φ d + κ * b + C) + ((Finset.univ \ tried).card : ℝ≥0∞)⁻¹ * (lam *
              ∑ η ∈ Finset.univ \ tried, (if m ++ η ∈ W P d then (1 : ℝ≥0∞) else 0)) := by
            rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
              ← Finset.mul_sum, mul_add, ← mul_assoc, ENNReal.inv_mul_cancel hc0 hct, one_mul]
        _ ≤ (Φ d + κ * b + C) + ((2 ^ P.nonceBits - P.trialLimit : ℕ) : ℝ≥0∞)⁻¹ *
              (lam * pairs P d) :=
            add_le_add_right (mul_le_mul' (ENNReal.inv_le_inv.2 hDc) (mul_le_mul_right hsum _)) _
        _ = _ := by rw [hC]; push_cast; ring
    · rw [signIdxLoop, dif_neg hc, run_pure, E_pure]
      simp only [signIdxLoop, dif_neg hc, pure_bind] at hB
      refine (hF none d' b (signExt_none P hSub hNew) hI hB).trans ?_
      rw [hΦd, if_neg (not_exists_none P), mul_zero, add_zero]
      calc Φ d + κ * b = Φ d + 0 + κ * b := by rw [add_zero]
        _ ≤ _ := add_le_add_left (add_le_add_right zero_le _) _

/-- **The signing bound.** -/
theorem signIdx_bound (hM : 0 < P.numSets) (hM' : P.numSets ≤ 2 ^ P.idxBits)
    (hidx : P.idxBits ≤ P.hashBits) (hL : P.trialLimit < 2 ^ P.nonceBits)
    (m : Message P) (d : Cache P) {β J : Type} [Nonempty J]
    (k : J → Option (Nonce P × Fin P.numSets) → OracleComp (Spec P) β)
    (F : Option (Nonce P × Fin P.numSets) → Cache P → ℝ≥0∞)
    (Φ : Cache P → ℝ≥0∞) (hΦ : EncInvariant P Φ) (κ lam : ℝ≥0∞)
    (I : Cache P → ℕ → Prop)
    (hI_fresh : ∀ c b q, I c b → c q = none → queryCost P (.inr q) ≤ b →
      ∀ u, I (c.cacheQuery q u) (b - queryCost P (.inr q)))
    (hI_cached : ∀ c b q, I c b → (c q).isSome → queryCost P (.inr q) ≤ b →
      I c (b - queryCost P (.inr q)))
    (hF : ∀ r d' b', SignExt P m d r d' → I d' b' → (∀ j, CostAtMost P (k j r) b') →
      F r d' ≤ Φ d' + lam * (if ∃ η i, r = some (η, i) ∧ IdxPre P d (m ++ η) i.val then 1 else 0) +
        κ * b')
    {b : ℕ} (hI : I d b) (hB : ∀ j, CostAtMost P (signIdx P m >>= k j) b) :
    E (run P (signIdx P m) d) (fun p => F p.1 p.2) ≤
      Φ d + lam * ((cntV P d : ℝ≥0∞) / P.numSets +
        (P.trialLimit : ℝ≥0∞) * pairs P d / ((2 ^ P.nonceBits - P.trialLimit : ℕ) : ℝ≥0∞)) +
        κ * b := by
  have h := signIdxLoop_bound P hM hM' hidx hL m d k F Φ hΦ κ lam I hI_fresh hI_cached hF
    P.trialLimit ∅ d b (Cache.Sub.refl d) (fun q w h1 h2 => by rw [h1] at h2; cases h2) rfl
    (by simp) hI hB
  refine h.trans (le_of_eq ?_)
  rw [ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul]
  ring

end OptimalOTS
