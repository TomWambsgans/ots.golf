import Submissions.Upper.SignRho

/-!
# Rows of the encoding cache

The encoding entries `m ++ η` of a cache, grouped by message `m` (a *row*): the cached nonces
`rowCached`, the accepted ones `rowAcc`, the accepted ones sharing their index `rowBad`, and the
non-shared accepted ones with a given index `rowHit`. How they change when one fresh encoding answer
is cached (`*_cacheQuery`), and the two global counts used by the potential: non-shared accepted
entries hold distinct indices (`sum_rowFree_le`) and rows partition the encoding entries
(`sum_rowCached_le`).
-/

open OracleSpec OracleComp ENNReal

noncomputable section

open scoped Classical

namespace OptimalOTS

variable (P : Params)

theorem append_pair_inj {m m' : Message P} {η η' : Nonce P} (h : m ++ η = m' ++ η') :
    m = m' ∧ η = η' := by
  have key : ∀ i, (m ++ η).getLsbD i = (m' ++ η').getLsbD i := fun i => by rw [h]
  simp only [BitVec.getLsbD_append] at key
  constructor
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have := key (i + P.nonceBits)
    simp only [show ¬ (i + P.nonceBits < P.nonceBits) by omega, if_false, Nat.add_sub_cancel]
      at this
    exact this
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have := key i
    simp only [hi, if_true] at this
    exact this

theorem exists_append (u : EncInput P) : ∃ (m : Message P) (η : Nonce P), u = m ++ η := by
  refine ⟨u.extractLsb' P.nonceBits P.msgBits, u.setWidth P.nonceBits, ?_⟩
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_append]
  split_ifs with h
  · simp [BitVec.getLsbD_setWidth, h]
  · rw [BitVec.getLsbD_extractLsb']
    have : i - P.nonceBits < P.msgBits := by omega
    simp [this, show P.nonceBits + (i - P.nonceBits) = i by omega]

/-- Cached nonces of row `m`. -/
def rowCached (d : Cache P) (m : Message P) : Finset (Nonce P) :=
  Finset.univ.filter fun η => (d (encQuery P (m ++ η))).isSome

/-- Accepted nonces of row `m` with index `i` that no other entry shares. -/
def rowHit (d : Cache P) (m : Message P) (i : ℕ) : Finset (Nonce P) :=
  Finset.univ.filter fun η => ∃ w, d (encQuery P (m ++ η)) = some w ∧ idxOf P w < P.numSets ∧
    ¬ IdxPre P d (m ++ η) (idxOf P w) ∧ idxOf P w = i

theorem mem_V_iff {d : Cache P} {i : ℕ} :
    i ∈ V P d ↔ ∃ u w, d (encQuery P u) = some w ∧ idxOf P w < P.numSets ∧ idxOf P w = i := by
  constructor
  · intro h
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 h
    simp only [validSet, Finset.mem_filter, Finset.mem_univ, true_and] at hu
    obtain ⟨w, hw, hi⟩ := hu
    exact ⟨u, w, hw, hi, by simp [hw]⟩
  · rintro ⟨u, w, hw, hi, rfl⟩
    exact mem_V P hw hi

theorem V_lt_numSets (d : Cache P) : ∀ i ∈ V P d, i < P.numSets := by
  intro i hi
  obtain ⟨u, w, -, hw, rfl⟩ := (mem_V_iff P).1 hi
  exact hw

theorem card_V_le_numSets (d : Cache P) : (V P d).card ≤ P.numSets := by
  calc (V P d).card ≤ (Finset.range P.numSets).card :=
        Finset.card_le_card fun i hi => Finset.mem_range.2 (V_lt_numSets P d i hi)
    _ = P.numSets := Finset.card_range _

theorem rowHit_subset (d : Cache P) (m : Message P) (i : ℕ) :
    rowHit P d m i ⊆ rowAcc P d m \ rowBad P d m := by
  intro η hη
  simp only [rowHit, Finset.mem_filter, Finset.mem_univ, true_and] at hη
  obtain ⟨w, hw, hi, hn, -⟩ := hη
  simp only [Finset.mem_sdiff, rowAcc, rowBad, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨⟨w, hw, hi⟩, ?_⟩
  rintro ⟨w', hw', -, hpre⟩
  rw [hw] at hw'
  cases hw'
  exact hn hpre

theorem rowHit_eq_empty (d : Cache P) (m : Message P) {i : ℕ} (hi : i ∉ V P d) :
    rowHit P d m i = ∅ := by
  ext η
  simp only [rowHit, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
    iff_false]
  rintro ⟨w, hw, hv, -, rfl⟩
  exact hi (mem_V P hw hv)

/-- Every non-shared accepted entry of row `m` has its index in `V`. -/
theorem sum_rowHit (d : Cache P) (m : Message P) :
    ∑ i ∈ V P d, (rowHit P d m i).card = (rowAcc P d m \ rowBad P d m).card := by
  have hdisj : ∀ i ∈ V P d, ∀ j ∈ V P d, i ≠ j → Disjoint (rowHit P d m i) (rowHit P d m j) := by
    intro i _ j _ hij
    rw [Finset.disjoint_left]
    intro η h1 h2
    simp only [rowHit, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
    obtain ⟨w, hw, -, -, rfl⟩ := h1
    obtain ⟨w', hw', -, -, rfl⟩ := h2
    rw [hw] at hw'
    cases hw'
    exact hij rfl
  rw [← Finset.card_biUnion hdisj]
  congr 1
  ext η
  simp only [Finset.mem_biUnion, Finset.mem_sdiff]
  constructor
  · rintro ⟨i, -, hη⟩
    exact Finset.mem_sdiff.1 (rowHit_subset P d m i hη)
  · rintro ⟨hacc, hbad⟩
    simp only [rowAcc, Finset.mem_filter, Finset.mem_univ, true_and] at hacc
    obtain ⟨w, hw, hi⟩ := hacc
    refine ⟨idxOf P w, mem_V P hw hi, ?_⟩
    simp only [rowHit, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨w, hw, hi, fun hpre => hbad ?_, rfl⟩
    simp only [rowBad, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨w, hw, hi, hpre⟩

/-- Non-shared accepted entries of all rows hold distinct indices. -/
theorem sum_rowFree_le (d : Cache P) :
    ∑ m, (rowAcc P d m \ rowBad P d m).card ≤ (V P d).card := by
  rw [← Finset.card_sigma]
  refine Finset.card_le_card_of_injOn
    (fun p => ((d (encQuery P (p.1 ++ p.2))).map (idxOf P)).getD 0) ?_ ?_
  · intro p hp
    simp only [Finset.coe_sigma, Set.mem_sigma_iff, Finset.mem_coe, Finset.mem_univ,
      true_and, Finset.mem_sdiff, rowAcc, Finset.mem_filter] at hp
    obtain ⟨⟨w, hw, hi⟩, -⟩ := hp
    simp only [Finset.mem_coe, hw, Option.map_some, Option.getD_some]
    exact mem_V P hw hi
  · intro p hp p' hp' heq
    simp only [Finset.coe_sigma, Set.mem_sigma_iff, Finset.mem_coe, Finset.mem_univ,
      true_and, Finset.mem_sdiff, rowAcc, rowBad, Finset.mem_filter] at hp hp'
    obtain ⟨⟨w, hw, hi⟩, hn⟩ := hp
    obtain ⟨⟨w', hw', hi'⟩, -⟩ := hp'
    simp only [hw, hw', Option.map_some, Option.getD_some] at heq
    by_contra hne
    apply hn
    refine ⟨w, hw, hi, p'.1 ++ p'.2, ?_, w', hw', heq.symm⟩
    intro he
    apply hne
    obtain ⟨h1, h2⟩ := append_pair_inj P he
    exact Sigma.ext h1.symm (heq_of_eq h2.symm)

/-- Rows partition the encoding entries. -/
theorem sum_rowCached_le (d : Cache P) :
    ∑ m, (rowCached P d m).card ≤ encCount P d := by
  rw [← Finset.card_sigma]
  refine Finset.card_le_card_of_injOn (fun p => p.1 ++ p.2) ?_ ?_
  · intro p hp
    simp only [Finset.coe_sigma, Set.mem_sigma_iff, Finset.mem_coe, Finset.mem_univ,
      true_and, rowCached, Finset.mem_filter] at hp
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
    exact hp
  · intro p _ p' _ heq
    obtain ⟨h1, h2⟩ := append_pair_inj P heq
    exact Sigma.ext h1 (heq_of_eq h2)

/-! ## One fresh encoding answer -/

section Step

variable {P} {d : Cache P} {m₀ : Message P} {η₀ : Nonce P} (w : BitVec P.hashBits)

theorem cacheQuery_enc_apply (m : Message P) (η : Nonce P) :
    (d.cacheQuery (encQuery P (m₀ ++ η₀)) w) (encQuery P (m ++ η)) =
      if m = m₀ ∧ η = η₀ then some w else d (encQuery P (m ++ η)) := by
  split_ifs with h
  · obtain ⟨rfl, rfl⟩ := h
    exact QueryCache.cacheQuery_self _ _ _
  · refine QueryCache.cacheQuery_of_ne _ _ fun he => h ?_
    exact append_pair_inj P (encQuery_inj P he)

variable (hfresh : d (encQuery P (m₀ ++ η₀)) = none)
include hfresh

theorem rowCached_cacheQuery (m : Message P) :
    (rowCached P (d.cacheQuery (encQuery P (m₀ ++ η₀)) w) m).card =
      (rowCached P d m).card + if m = m₀ then 1 else 0 := by
  by_cases hm : m = m₀
  · subst hm
    rw [if_pos rfl]
    have hnot : η₀ ∉ rowCached P d m := by
      simp [rowCached, hfresh]
    have : rowCached P (d.cacheQuery (encQuery P (m ++ η₀)) w) m = insert η₀ (rowCached P d m) := by
      ext η
      simp only [rowCached, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        cacheQuery_enc_apply]
      by_cases h : η = η₀ <;> simp [h]
    rw [this, Finset.card_insert_of_notMem hnot]
  · rw [if_neg hm, add_zero]
    congr 1
    ext η
    simp only [rowCached, Finset.mem_filter, Finset.mem_univ, true_and, cacheQuery_enc_apply,
      hm, false_and, if_false]

theorem rowAcc_cacheQuery (m : Message P) :
    (rowAcc P (d.cacheQuery (encQuery P (m₀ ++ η₀)) w) m).card =
      (rowAcc P d m).card + if m = m₀ ∧ idxOf P w < P.numSets then 1 else 0 := by
  by_cases hm : m = m₀ ∧ idxOf P w < P.numSets
  · obtain ⟨rfl, hi⟩ := hm
    rw [if_pos ⟨rfl, hi⟩]
    have hnot : η₀ ∉ rowAcc P d m := by
      simp [rowAcc, hfresh]
    have : rowAcc P (d.cacheQuery (encQuery P (m ++ η₀)) w) m = insert η₀ (rowAcc P d m) := by
      ext η
      simp only [rowAcc, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        cacheQuery_enc_apply]
      by_cases h : η = η₀
      · simp [h, hi]
      · simp [h]
    rw [this, Finset.card_insert_of_notMem hnot]
  · rw [if_neg hm, add_zero]
    congr 1
    ext η
    simp only [rowAcc, Finset.mem_filter, Finset.mem_univ, true_and, cacheQuery_enc_apply]
    by_cases h : m = m₀ ∧ η = η₀
    · obtain ⟨rfl, rfl⟩ := h
      simp only [and_self, if_true, Option.some.injEq, exists_eq_left', hfresh, reduceCtorEq,
        false_and, exists_false, iff_false]
      exact fun hi => hm ⟨rfl, hi⟩
    · simp only [h, if_false]

theorem V_cacheQuery :
    (V P (d.cacheQuery (encQuery P (m₀ ++ η₀)) w)).card =
      (V P d).card + if idxOf P w < P.numSets ∧ idxOf P w ∉ V P d then 1 else 0 := by
  have hmem : ∀ i, i ∈ V P (d.cacheQuery (encQuery P (m₀ ++ η₀)) w) ↔
      i ∈ V P d ∨ (idxOf P w < P.numSets ∧ idxOf P w = i) := by
    intro i
    rw [mem_V_iff, mem_V_iff]
    constructor
    · rintro ⟨u, w', hu, hi, rfl⟩
      by_cases he : u = m₀ ++ η₀
      · subst he
        rw [QueryCache.cacheQuery_self] at hu
        cases hu
        exact Or.inr ⟨hi, rfl⟩
      · rw [QueryCache.cacheQuery_of_ne _ _ (fun h => he (encQuery_inj P h))] at hu
        exact Or.inl ⟨u, w', hu, hi, rfl⟩
    · rintro (⟨u, w', hu, hi, rfl⟩ | ⟨hi, rfl⟩)
      · have hne : u ≠ m₀ ++ η₀ := by
          rintro rfl
          rw [hfresh] at hu
          cases hu
        refine ⟨u, w', ?_, hi, rfl⟩
        rw [QueryCache.cacheQuery_of_ne _ _ (fun h => hne (encQuery_inj P h))]
        exact hu
      · exact ⟨m₀ ++ η₀, w, QueryCache.cacheQuery_self _ _ _, hi, rfl⟩
  split_ifs with h
  · have : V P (d.cacheQuery (encQuery P (m₀ ++ η₀)) w) = insert (idxOf P w) (V P d) := by
      ext i
      rw [hmem, Finset.mem_insert]
      constructor
      · rintro (h' | ⟨-, rfl⟩)
        · exact Or.inr h'
        · exact Or.inl rfl
      · rintro (rfl | h')
        · exact Or.inr ⟨h.1, rfl⟩
        · exact Or.inl h'
    rw [this, Finset.card_insert_of_notMem h.2]
  · rw [add_zero]
    congr 1
    ext i
    rw [hmem]
    constructor
    · rintro (h' | ⟨hi, rfl⟩)
      · exact h'
      · by_contra hn
        exact h ⟨hi, hn⟩
    · exact Or.inl

/-- A cached entry is shared after the answer only if it was shared before, or it is the new
entry (then its index was already held), or it holds the new index alone. -/
theorem rowBad_cacheQuery (m : Message P) :
    (rowBad P (d.cacheQuery (encQuery P (m₀ ++ η₀)) w) m).card ≤
      (rowBad P d m).card + (rowHit P d m (idxOf P w)).card +
        if m = m₀ ∧ idxOf P w ∈ V P d then 1 else 0 := by
  set d' := d.cacheQuery (encQuery P (m₀ ++ η₀)) w with hd'
  have hsub : rowBad P d' m ⊆ rowBad P d m ∪ rowHit P d m (idxOf P w) ∪
      (if m = m₀ ∧ idxOf P w ∈ V P d then {η₀} else ∅) := by
    intro η hη
    simp only [rowBad, Finset.mem_filter, Finset.mem_univ, true_and, hd',
      cacheQuery_enc_apply] at hη
    obtain ⟨w₁, hw₁, hi₁, u, hu, w₂, hw₂, hidx⟩ := hη
    by_cases hnew : m = m₀ ∧ η = η₀
    · obtain ⟨rfl, rfl⟩ := hnew
      simp only [and_self, if_true, Option.some.injEq] at hw₁
      subst hw₁
      apply Finset.mem_union_right
      have hu' : d (encQuery P u) = some w₂ := by
        rwa [QueryCache.cacheQuery_of_ne _ _ (fun h => hu (encQuery_inj P h))] at hw₂
      have hV : idxOf P w ∈ V P d := by
        rw [← hidx]; exact mem_V P hu' (hidx ▸ hi₁)
      rw [if_pos ⟨rfl, hV⟩]
      exact Finset.mem_singleton_self _
    · rw [if_neg hnew] at hw₁
      by_cases hu0 : u = m₀ ++ η₀
      · subst hu0
        rw [QueryCache.cacheQuery_self] at hw₂
        cases hw₂
        by_cases hpre : IdxPre P d (m ++ η) (idxOf P w₁)
        · refine Finset.mem_union_left _ (Finset.mem_union_left _ ?_)
          simp only [rowBad, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨w₁, hw₁, hi₁, hpre⟩
        · refine Finset.mem_union_left _ (Finset.mem_union_right _ ?_)
          simp only [rowHit, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨w₁, hw₁, hi₁, hpre, hidx.symm⟩
      · refine Finset.mem_union_left _ (Finset.mem_union_left _ ?_)
        simp only [rowBad, Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨w₁, hw₁, hi₁, u, hu, w₂, ?_, hidx⟩
        rwa [QueryCache.cacheQuery_of_ne _ _ (fun h => hu0 (encQuery_inj P h))] at hw₂
  refine (Finset.card_le_card hsub).trans ?_
  refine (Finset.card_union_le _ _).trans ?_
  refine add_le_add ((Finset.card_union_le _ _)) ?_
  split_ifs <;> simp

end Step

/-! ## Queries of other lengths leave the rows unchanged -/

section Other

variable {P} {d : Cache P} {q : Query} (hq : ∀ u : EncInput P, q ≠ encQuery P u)
  (w : BitVec P.hashBits)
include hq

theorem enc_apply_of_ne (u : EncInput P) : (d.cacheQuery q w) (encQuery P u) = d (encQuery P u) :=
  QueryCache.cacheQuery_of_ne _ _ (hq u).symm

theorem rowCached_of_ne (m : Message P) : rowCached P (d.cacheQuery q w) m = rowCached P d m := by
  simp only [rowCached, enc_apply_of_ne hq]

theorem rowAcc_of_ne (m : Message P) : rowAcc P (d.cacheQuery q w) m = rowAcc P d m := by
  simp only [rowAcc, enc_apply_of_ne hq]

theorem idxPre_of_ne (u : EncInput P) (i : ℕ) : IdxPre P (d.cacheQuery q w) u i ↔ IdxPre P d u i := by
  simp only [IdxPre, enc_apply_of_ne hq]

theorem rowBad_of_ne (m : Message P) : rowBad P (d.cacheQuery q w) m = rowBad P d m := by
  simp only [rowBad, enc_apply_of_ne hq, idxPre_of_ne hq]

theorem V_of_ne : V P (d.cacheQuery q w) = V P d := by
  ext i
  simp only [mem_V_iff, enc_apply_of_ne hq]

end Other

end OptimalOTS
