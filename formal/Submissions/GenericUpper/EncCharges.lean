import Submissions.GenericUpper.SignIdx

/-!
# Charges of encoding queries

The counting potentials of the signing analysis (`cntV`, `pairs`) and the event `IdxPost` (a new
encoding entry with a given index) only change at encoding queries, and a fresh encoding answer
changes them by a bounded amount on average:

* `cntV` grows by `numSets / 2 ^ idxBits`;
* `pairs` grows by `2 · encCount / 2 ^ idxBits`, where `encCount` is the number of encoding
  entries;
* a fresh encoding answer has a given index with probability `1 / 2 ^ idxBits`.

The oracle has no labels: an encoding query is a query of length `msgBits + nonceBits`
(`encQuery`), and a query of any other length is not one (`ne_encQuery_of_length_ne`), which is how
the hypothesis `∀ u, q ≠ encQuery P u` of the `_of_ne_enc` lemmas is discharged.
-/

open OracleSpec OracleComp ENNReal

noncomputable section

open scoped Classical

namespace OptimalOTS

variable (P : Params)

/-- Number of encoding entries of a cache. -/
def encCount (d : Cache P) : ℕ :=
  (Finset.univ.filter fun u : EncInput P => (d (encQuery P u)).isSome).card

/-- An encoding entry absent from `d'` is present in `c` with index `i`. -/
def IdxPost (d' c : Cache P) (i : ℕ) : Prop :=
  ∃ u, d' (encQuery P u) = none ∧ ∃ w, c (encQuery P u) = some w ∧ idxOf P w = i

theorem encCount_empty : encCount P ∅ = 0 := by
  simp [encCount]

theorem encCount_cacheQuery_le (d : Cache P) (q : Query) (w : BitVec P.hashBits) :
    encCount P (d.cacheQuery q w) ≤ encCount P d + 1 := by
  unfold encCount
  by_cases hq : ∃ u₀ : EncInput P, q = encQuery P u₀
  · obtain ⟨u₀, rfl⟩ := hq
    calc (Finset.univ.filter fun u : EncInput P =>
          ((d.cacheQuery (encQuery P u₀) w) (encQuery P u)).isSome).card
        ≤ (insert u₀ (Finset.univ.filter fun u : EncInput P =>
            (d (encQuery P u)).isSome)).card := by
          apply Finset.card_le_card
          intro u hu
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
          rw [Finset.mem_insert, Finset.mem_filter]
          by_cases h : u = u₀
          · exact Or.inl h
          · right
            refine ⟨Finset.mem_univ _, ?_⟩
            rwa [QueryCache.cacheQuery_of_ne _ _ (fun e => h (encQuery_inj P e))] at hu
      _ ≤ _ := Finset.card_insert_le _ _
  · simp only [not_exists] at hq
    have h : (Finset.univ.filter fun u : EncInput P =>
        ((d.cacheQuery q w) (encQuery P u)).isSome) =
        Finset.univ.filter fun u : EncInput P => (d (encQuery P u)).isSome := by
      apply Finset.filter_congr
      intro u _
      rw [QueryCache.cacheQuery_of_ne _ _ (Ne.symm (hq u))]
    rw [h]
    exact Nat.le_succ _

theorem encCount_mono {d d' : Cache P} (h : Cache.Sub d d') : encCount P d ≤ encCount P d' := by
  apply Finset.card_le_card
  intro u hu
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
  exact h.isSome hu

theorem cntV_cacheQuery_of_ne_enc (d : Cache P) {q : Query} (hq : ∀ u : EncInput P, q ≠ encQuery P u)
    (w : BitVec P.hashBits) : cntV P (d.cacheQuery q w) = cntV P d := by
  unfold cntV
  congr 1
  apply Finset.filter_congr
  intro u _
  rw [QueryCache.cacheQuery_of_ne _ _ (hq u).symm]

theorem pairs_cacheQuery_of_ne_enc (d : Cache P) {q : Query} (hq : ∀ u : EncInput P, q ≠ encQuery P u)
    (w : BitVec P.hashBits) : pairs P (d.cacheQuery q w) = pairs P d := by
  unfold pairs
  congr 1
  apply Finset.filter_congr
  intro p _
  rw [QueryCache.cacheQuery_of_ne _ _ (hq p.1).symm, QueryCache.cacheQuery_of_ne _ _ (hq p.2).symm]

theorem idxPost_cacheQuery_of_ne_enc (d' d : Cache P) {q : Query}
    (hq : ∀ u : EncInput P, q ≠ encQuery P u) (w : BitVec P.hashBits) (i : ℕ) :
    IdxPost P d' (d.cacheQuery q w) i ↔ IdxPost P d' d i := by
  have h : ∀ u : EncInput P, (d.cacheQuery q w) (encQuery P u) = d (encQuery P u) :=
    fun u => QueryCache.cacheQuery_of_ne _ _ (hq u).symm
  simp only [IdxPost, h]

theorem IdxPost.mono {d' c c' : Cache P} (h : Cache.Sub c c') {i : ℕ} (hi : IdxPost P d' c i) :
    IdxPost P d' c' i := by
  obtain ⟨u, hu, w, hw, hi⟩ := hi
  exact ⟨u, hu, w, h _ _ hw, hi⟩

theorem not_idxPost_extend_of_enc_none (d' f : Cache P) (hf : ∀ u : EncInput P, f (encQuery P u) = none)
    (i : ℕ) : ¬ IdxPost P d' (Cache.extend d' f) i := by
  rintro ⟨u, hu, w, hw, -⟩
  rw [Cache.extend_apply, hu, hf] at hw
  simp at hw

/-! ### Auxiliary counting facts -/

theorem idxOf_lt (w : BitVec P.hashBits) : idxOf P w < 2 ^ P.idxBits :=
  (w.setWidth P.idxBits).isLt

/-- Averaging `a * 2 ^ (hashBits - idxBits)` over the `2 ^ hashBits` answers gives `a / 2 ^ idxBits`. -/
theorem inv_card_mul_pow (hidx : P.idxBits ≤ P.hashBits) (a : ℝ≥0∞) :
    (Fintype.card (BitVec P.hashBits) : ℝ≥0∞)⁻¹ * (a * (2 ^ (P.hashBits - P.idxBits) : ℕ)) =
      a / 2 ^ P.idxBits := by
  have hc : (Fintype.card (BitVec P.hashBits) : ℝ≥0∞) =
      2 ^ P.idxBits * 2 ^ (P.hashBits - P.idxBits) := by
    rw [Fintype.card_bitVec, ← pow_add, Nat.add_sub_cancel' hidx]
    push_cast
    rfl
  have h2 : ((2 : ℝ≥0∞) ^ (P.hashBits - P.idxBits))⁻¹ * 2 ^ (P.hashBits - P.idxBits) = 1 :=
    ENNReal.inv_mul_cancel (by simp) (by simp)
  rw [hc, Nat.cast_pow, Nat.cast_ofNat, ENNReal.mul_inv (Or.inl (by simp)) (Or.inl (by simp)),
    div_eq_mul_inv]
  calc ((2 : ℝ≥0∞) ^ P.idxBits)⁻¹ * ((2 : ℝ≥0∞) ^ (P.hashBits - P.idxBits))⁻¹ *
        (a * 2 ^ (P.hashBits - P.idxBits))
      = a * ((2 : ℝ≥0∞) ^ P.idxBits)⁻¹ *
          (((2 : ℝ≥0∞) ^ (P.hashBits - P.idxBits))⁻¹ * 2 ^ (P.hashBits - P.idxBits)) := by ring
    _ = a * ((2 : ℝ≥0∞) ^ P.idxBits)⁻¹ := by rw [h2, mul_one]

/-- The number of answers with a given index is at most `2 ^ (hashBits - idxBits)`. -/
theorem card_idxOf_eq_le (hidx : P.idxBits ≤ P.hashBits) (i : ℕ) :
    (Finset.univ.filter fun w : BitVec P.hashBits => idxOf P w = i).card ≤
      2 ^ (P.hashBits - P.idxBits) := by
  have h1 : (Finset.univ.filter fun w : BitVec P.hashBits => idxOf P w = i) =
      Finset.univ.filter fun w : BitVec P.hashBits =>
        idxOf P w ∈ ({i} : Finset ℕ).filter fun n => n < 2 ^ P.idxBits := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · rintro rfl
      exact ⟨rfl, idxOf_lt P w⟩
    · rintro ⟨h, -⟩
      exact h
  rw [h1, card_idxOf_mem P hidx _ (fun n hn => (Finset.mem_filter.1 hn).2)]
  calc _ ≤ 1 * 2 ^ (P.hashBits - P.idxBits) :=
        Nat.mul_le_mul_right _ (le_trans (Finset.card_filter_le _ _) (by simp))
    _ = _ := one_mul _

/-- The number of answers with a given index, when that index is in range. -/
theorem card_idxOf_eq (hidx : P.idxBits ≤ P.hashBits) (w' : BitVec P.hashBits) :
    (Finset.univ.filter fun w : BitVec P.hashBits => idxOf P w' = idxOf P w).card =
      2 ^ (P.hashBits - P.idxBits) := by
  have h1 : (Finset.univ.filter fun w : BitVec P.hashBits => idxOf P w' = idxOf P w) =
      Finset.univ.filter fun w : BitVec P.hashBits => idxOf P w ∈ ({idxOf P w'} : Finset ℕ) := by
    ext w
    simp [eq_comm]
  rw [h1, card_idxOf_mem P hidx _ (by simpa using idxOf_lt P w'), Finset.card_singleton, one_mul]

/-! ### `cntV` -/

/-- A fresh encoding answer adds one valid entry iff its index is valid. -/
theorem cntV_cacheQuery_enc (d : Cache P) (u : EncInput P) (hq : d (encQuery P u) = none)
    (w : BitVec P.hashBits) :
    cntV P (d.cacheQuery (encQuery P u) w) =
      cntV P d + if idxOf P w < P.numSets then 1 else 0 := by
  unfold cntV
  have hu : u ∉ Finset.univ.filter fun u' : EncInput P =>
      ∃ w, d (encQuery P u') = some w ∧ idxOf P w < P.numSets := by
    simp [hq]
  have hne : ∀ u' : EncInput P, u' ≠ u →
      (d.cacheQuery (encQuery P u) w) (encQuery P u') = d (encQuery P u') :=
    fun u' h => QueryCache.cacheQuery_of_ne _ _ (fun e => h (encQuery_inj P e))
  split_ifs with hw
  · rw [← Finset.card_insert_of_notMem hu]
    congr 1
    ext u'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    by_cases h : u' = u
    · rw [h]
      simp [hw]
    · rw [hne u' h]
      simp [h]
  · rw [add_zero]
    congr 1
    apply Finset.filter_congr
    intro u' _
    by_cases h : u' = u
    · rw [h]
      simp [hq, hw]
    · rw [hne u' h]

/-- A fresh encoding answer is valid with probability `numSets / 2 ^ idxBits`. -/
theorem cntV_charge (hidx : P.idxBits ≤ P.hashBits) (hM : P.numSets ≤ 2 ^ P.idxBits) (d : Cache P)
    (u : EncInput P) (hq : d (encQuery P u) = none) :
    ∑ w : BitVec P.hashBits, (Fintype.card (BitVec P.hashBits) : ℝ≥0∞)⁻¹ *
        (cntV P (d.cacheQuery (encQuery P u) w) : ℝ≥0∞) ≤
      cntV P d + (P.numSets : ℝ≥0∞) / 2 ^ P.idxBits := by
  have hval : (∑ w : BitVec P.hashBits, if idxOf P w < P.numSets then (1 : ℝ≥0∞) else 0) =
      (P.numSets : ℝ≥0∞) * (2 ^ (P.hashBits - P.idxBits) : ℕ) := by
    rw [Finset.sum_boole]
    have h1 : (Finset.univ.filter fun w : BitVec P.hashBits => idxOf P w < P.numSets) =
        Finset.univ.filter fun w : BitVec P.hashBits => idxOf P w ∈ Finset.range P.numSets := by
      ext w; simp
    rw [h1, card_idxOf_mem P hidx _ (fun n hn => lt_of_lt_of_le (Finset.mem_range.1 hn) hM),
      Finset.card_range, Nat.cast_mul]
  simp only [cntV_cacheQuery_enc P d u hq, Nat.cast_add, Nat.cast_ite, Nat.cast_one,
    Nat.cast_zero, mul_add, Finset.sum_add_distrib, sum_inv_card_mul]
  rw [← Finset.mul_sum, hval, inv_card_mul_pow P hidx]

/-! ### `pairs` -/

/-- Entries of `d` whose index equals `idxOf P w`. -/
def collSet (d : Cache P) (w : BitVec P.hashBits) : Finset (EncInput P) :=
  Finset.univ.filter fun u' : EncInput P =>
    ∃ w', d (encQuery P u') = some w' ∧ idxOf P w' = idxOf P w

/-- A fresh encoding answer creates two ordered pairs per colliding entry. -/
theorem pairs_cacheQuery_enc (d : Cache P) (u : EncInput P) (hq : d (encQuery P u) = none)
    (w : BitVec P.hashBits) :
    pairs P (d.cacheQuery (encQuery P u) w) = pairs P d + 2 * (collSet P d w).card := by
  set D := d.cacheQuery (encQuery P u) w with hD
  have hDu : D (encQuery P u) = some w := QueryCache.cacheQuery_self _ _ _
  have hDne : ∀ u' : EncInput P, u' ≠ u → D (encQuery P u') = d (encQuery P u') :=
    fun u' h => QueryCache.cacheQuery_of_ne _ _ (fun e => h (encQuery_inj P e))
  have hne_of_some : ∀ (u' : EncInput P) (w' : BitVec P.hashBits),
      d (encQuery P u') = some w' → u' ≠ u := by
    rintro u' w' h rfl
    rw [hq] at h
    cases h
  have hmem : ∀ u', u' ∈ collSet P d w ↔
      ∃ w', d (encQuery P u') = some w' ∧ idxOf P w' = idxOf P w := by
    intro u'; simp [collSet]
  have key : ∀ p : EncInput P × EncInput P,
      (p.1 ≠ p.2 ∧ ∃ w₁ w₂, D (encQuery P p.1) = some w₁ ∧ D (encQuery P p.2) = some w₂ ∧
        idxOf P w₁ = idxOf P w₂) ↔
      ((p.1 ≠ p.2 ∧ ∃ w₁ w₂, d (encQuery P p.1) = some w₁ ∧ d (encQuery P p.2) = some w₂ ∧
        idxOf P w₁ = idxOf P w₂) ∨ (p.1 = u ∧ p.2 ∈ collSet P d w)) ∨
        (p.2 = u ∧ p.1 ∈ collSet P d w) := by
    rintro ⟨a, b⟩
    simp only [hmem]
    constructor
    · rintro ⟨hab, w₁, w₂, h₁, h₂, h₁₂⟩
      by_cases ha : a = u
      · have hb : b ≠ u := fun e => hab (ha.trans e.symm)
        rw [ha, hDu] at h₁
        rw [hDne b hb] at h₂
        refine Or.inl (Or.inr ⟨ha, w₂, h₂, ?_⟩)
        rw [← h₁₂, Option.some.inj h₁]
      · by_cases hb : b = u
        · rw [hb, hDu] at h₂
          rw [hDne a ha] at h₁
          refine Or.inr ⟨hb, w₁, h₁, ?_⟩
          rw [h₁₂, Option.some.inj h₂]
        · rw [hDne a ha] at h₁
          rw [hDne b hb] at h₂
          exact Or.inl (Or.inl ⟨hab, w₁, w₂, h₁, h₂, h₁₂⟩)
    · rintro ((⟨hab, w₁, w₂, h₁, h₂, h₁₂⟩ | ⟨ha, w₂, h₂, h₂w⟩) | ⟨hb, w₁, h₁, h₁w⟩)
      · exact ⟨hab, w₁, w₂, by rw [hDne a (hne_of_some a w₁ h₁)]; exact h₁,
          by rw [hDne b (hne_of_some b w₂ h₂)]; exact h₂, h₁₂⟩
      · have hb := hne_of_some b w₂ h₂
        exact ⟨fun e => hb (e.symm.trans ha), w, w₂, by rw [ha]; exact hDu,
          by rw [hDne b hb]; exact h₂, h₂w.symm⟩
      · have ha := hne_of_some a w₁ h₁
        exact ⟨fun e => ha (e.trans hb), w₁, w, by rw [hDne a ha]; exact h₁,
          by rw [hb]; exact hDu, h₁w⟩
  have hA : ((Finset.univ ×ˢ Finset.univ).filter fun p : EncInput P × EncInput P =>
      p.1 = u ∧ p.2 ∈ collSet P d w) = {u} ×ˢ collSet P d w := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and,
      Finset.mem_singleton]
  have hB : ((Finset.univ ×ˢ Finset.univ).filter fun p : EncInput P × EncInput P =>
      p.2 = u ∧ p.1 ∈ collSet P d w) = collSet P d w ×ˢ {u} := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and,
      Finset.mem_singleton]
    exact and_comm
  have hdisj₁ : Disjoint
      ((Finset.univ ×ˢ Finset.univ).filter fun p : EncInput P × EncInput P =>
        p.1 ≠ p.2 ∧ ∃ w₁ w₂, d (encQuery P p.1) = some w₁ ∧ d (encQuery P p.2) = some w₂ ∧
          idxOf P w₁ = idxOf P w₂)
      ((Finset.univ ×ˢ Finset.univ).filter fun p : EncInput P × EncInput P =>
        p.1 = u ∧ p.2 ∈ collSet P d w) := by
    rw [Finset.disjoint_left]
    rintro ⟨a, b⟩ h₁ h₂
    simp only [Finset.mem_filter] at h₁ h₂
    obtain ⟨-, -, w₁, w₂, ha, -, -⟩ := h₁
    exact hne_of_some a w₁ ha h₂.2.1
  have hdisj₂ : Disjoint
      (((Finset.univ ×ˢ Finset.univ).filter fun p : EncInput P × EncInput P =>
        p.1 ≠ p.2 ∧ ∃ w₁ w₂, d (encQuery P p.1) = some w₁ ∧ d (encQuery P p.2) = some w₂ ∧
          idxOf P w₁ = idxOf P w₂) ∪
        ((Finset.univ ×ˢ Finset.univ).filter fun p : EncInput P × EncInput P =>
          p.1 = u ∧ p.2 ∈ collSet P d w))
      ((Finset.univ ×ˢ Finset.univ).filter fun p : EncInput P × EncInput P =>
        p.2 = u ∧ p.1 ∈ collSet P d w) := by
    rw [Finset.disjoint_left]
    rintro ⟨a, b⟩ h₁ h₂
    simp only [Finset.mem_filter, Finset.mem_union] at h₁ h₂
    obtain ⟨-, hb, ha⟩ := h₂
    rw [hmem] at ha
    obtain ⟨w₁, ha, -⟩ := ha
    rcases h₁ with ⟨-, -, w₁', w₂, -, hb', -⟩ | ⟨-, hau, hbc⟩
    · exact hne_of_some b w₂ hb' hb
    · rw [hmem] at hbc
      obtain ⟨w₂, hb', -⟩ := hbc
      exact hne_of_some b w₂ hb' hb
  unfold pairs
  rw [Finset.filter_congr (fun p _ => key p), Finset.filter_or, Finset.filter_or,
    Finset.card_union_of_disjoint hdisj₂, Finset.card_union_of_disjoint hdisj₁, hA, hB,
    Finset.card_product, Finset.card_product, Finset.card_singleton]
  ring

/-- Summing the collision counts over all answers counts each entry `2 ^ (hashBits - idxBits)`
times. -/
theorem sum_card_collSet (hidx : P.idxBits ≤ P.hashBits) (d : Cache P) :
    ∑ w : BitVec P.hashBits, (collSet P d w).card =
      encCount P d * 2 ^ (P.hashBits - P.idxBits) := by
  simp only [collSet, Finset.card_filter]
  rw [Finset.sum_comm]
  unfold encCount
  rw [Finset.card_filter, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro u' _
  rcases h : d (encQuery P u') with _ | w'
  · simp
  · simp only [Option.isSome_some, if_true, one_mul, Option.some.injEq, exists_eq_left']
    rw [← Finset.card_filter, card_idxOf_eq P hidx w']

/-- A fresh encoding answer collides with each existing entry with probability `1 / 2 ^ idxBits`,
creating two ordered pairs each time. -/
theorem pairs_charge (hidx : P.idxBits ≤ P.hashBits) (d : Cache P) (u : EncInput P)
    (hq : d (encQuery P u) = none) :
    ∑ w : BitVec P.hashBits, (Fintype.card (BitVec P.hashBits) : ℝ≥0∞)⁻¹ *
        (pairs P (d.cacheQuery (encQuery P u) w) : ℝ≥0∞) ≤
      pairs P d + 2 * (encCount P d : ℝ≥0∞) / 2 ^ P.idxBits := by
  have hsum : (∑ w : BitVec P.hashBits, ((collSet P d w).card : ℝ≥0∞)) =
      (encCount P d : ℝ≥0∞) * (2 ^ (P.hashBits - P.idxBits) : ℕ) := by
    rw [← Nat.cast_sum, sum_card_collSet P hidx d, Nat.cast_mul]
  simp only [pairs_cacheQuery_enc P d u hq, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, mul_add,
    Finset.sum_add_distrib, sum_inv_card_mul]
  rw [← Finset.mul_sum, ← Finset.mul_sum, hsum,
    mul_left_comm (Fintype.card (BitVec P.hashBits) : ℝ≥0∞)⁻¹, inv_card_mul_pow P hidx,
    mul_div_assoc]

/-! ### `IdxPost` -/

/-- A fresh encoding answer at `u` realises `IdxPost` (when it did not hold before) iff `u` is
absent from `d'` and the answer has index `i`. -/
theorem idxPost_cacheQuery_enc {d' d : Cache P} (u : EncInput P) (w : BitVec P.hashBits) {i : ℕ}
    (h : ¬ IdxPost P d' d i) :
    IdxPost P d' (d.cacheQuery (encQuery P u) w) i ↔ d' (encQuery P u) = none ∧ idxOf P w = i := by
  constructor
  · rintro ⟨u', hu', w', hw', hi⟩
    by_cases hu : u' = u
    · rw [hu, QueryCache.cacheQuery_self] at hw'
      rw [hu] at hu'
      exact ⟨hu', by rw [Option.some.inj hw']; exact hi⟩
    · rw [QueryCache.cacheQuery_of_ne _ _ (fun e => hu (encQuery_inj P e))] at hw'
      exact absurd ⟨u', hu', w', hw', hi⟩ h
  · rintro ⟨hu, hi⟩
    exact ⟨u, hu, w, QueryCache.cacheQuery_self _ _ _, hi⟩

-- The bound does not use that `u` is fresh in `d` (`hq` is part of the fixed interface).
set_option linter.unusedVariables false in
/-- A fresh encoding answer has index `i` with probability `1 / 2 ^ idxBits`. -/
theorem idxPost_charge (hidx : P.idxBits ≤ P.hashBits) (d' d : Cache P) (u : EncInput P)
    (hq : d (encQuery P u) = none) (i : ℕ) :
    ∑ w : BitVec P.hashBits, (Fintype.card (BitVec P.hashBits) : ℝ≥0∞)⁻¹ *
        (if IdxPost P d' (d.cacheQuery (encQuery P u) w) i then 1 else 0) ≤
      (if IdxPost P d' d i then 1 else 0) + ((2 : ℝ≥0∞) ^ P.idxBits)⁻¹ := by
  by_cases h : IdxPost P d' d i
  · rw [if_pos h]
    calc ∑ w : BitVec P.hashBits, (Fintype.card (BitVec P.hashBits) : ℝ≥0∞)⁻¹ *
          (if IdxPost P d' (d.cacheQuery (encQuery P u) w) i then 1 else 0)
        ≤ ∑ w : BitVec P.hashBits, (Fintype.card (BitVec P.hashBits) : ℝ≥0∞)⁻¹ * 1 :=
          Finset.sum_le_sum fun w _ => mul_le_mul_right (by split_ifs <;> simp) _
      _ = 1 := sum_inv_card_mul 1
      _ ≤ 1 + ((2 : ℝ≥0∞) ^ P.idxBits)⁻¹ := le_self_add
  · rw [if_neg h, zero_add]
    have hle : ∀ w : BitVec P.hashBits,
        (if IdxPost P d' (d.cacheQuery (encQuery P u) w) i then (1 : ℝ≥0∞) else 0) ≤
          if idxOf P w = i then 1 else 0 := by
      intro w
      rw [idxPost_cacheQuery_enc P u w h]
      split_ifs with h₁ h₂ h₂
      · exact le_rfl
      · exact absurd h₁.2 h₂
      · exact zero_le
      · exact le_rfl
    calc ∑ w : BitVec P.hashBits, (Fintype.card (BitVec P.hashBits) : ℝ≥0∞)⁻¹ *
          (if IdxPost P d' (d.cacheQuery (encQuery P u) w) i then 1 else 0)
        ≤ ∑ w : BitVec P.hashBits, (Fintype.card (BitVec P.hashBits) : ℝ≥0∞)⁻¹ *
            (if idxOf P w = i then 1 else 0) :=
          Finset.sum_le_sum fun w _ => mul_le_mul_right (hle w) _
      _ = (Fintype.card (BitVec P.hashBits) : ℝ≥0∞)⁻¹ *
            ((Finset.univ.filter fun w : BitVec P.hashBits => idxOf P w = i).card : ℝ≥0∞) := by
          rw [← Finset.mul_sum, Finset.sum_boole]
      _ ≤ (Fintype.card (BitVec P.hashBits) : ℝ≥0∞)⁻¹ *
            (1 * (2 ^ (P.hashBits - P.idxBits) : ℕ)) := by
          rw [one_mul]
          exact mul_le_mul_right (Nat.cast_le.2 (card_idxOf_eq_le P hidx i)) _
      _ = ((2 : ℝ≥0∞) ^ P.idxBits)⁻¹ := by
          rw [inv_card_mul_pow P hidx, one_div]

end OptimalOTS
