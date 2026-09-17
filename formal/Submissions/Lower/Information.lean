import Submissions.Lower.Entropy

/-!
# The information bound

Records are pairs `ξ = (z, y)` of a secret part `z : Z` and outputs `y : Fin n → Out`, chosen
uniformly. An observer sees `X ξ : Obs`, a type with at most `2 ^ ℓ` elements, and the outputs
`y k` for `k ∈ E`. The candidate set of `ξ` is the set of records giving the same observation.
The weight of an unobserved output `k` is `log₂ |Out| - H(y k | z, y_{<k})` for a uniform
candidate. The total weight exceeds `ℓ + u` with probability at most `2 ^ (-u)`.
-/

open scoped Classical

namespace OptimalOTS

/-- The records giving the same observation as `ξ`. -/
noncomputable def candidates {Z Obs Out : Type*} [Fintype Z] [Fintype Out] {n : ℕ}
    (E : Finset (Fin n)) (X : Z × (Fin n → Out) → Obs) (ξ : Z × (Fin n → Out)) :
    Finset (Z × (Fin n → Out)) :=
  Finset.univ.filter fun ξ' => X ξ' = X ξ ∧ ∀ k ∈ E, ξ'.2 k = ξ.2 k

/-- The outputs before `k`, with the others hidden. -/
def outputsBefore {Out : Type*} {n : ℕ} (y : Fin n → Out) (k : Fin n) : Fin n → Option Out :=
  fun j => if j < k then some (y j) else none

/-- The weight of output `k` given the observation of `ξ`. -/
noncomputable def infoWeight {Z Obs Out : Type*} [Fintype Z] [Fintype Out] {n : ℕ}
    (E : Finset (Fin n)) (X : Z × (Fin n → Out) → Obs) (ξ : Z × (Fin n → Out)) (k : Fin n) : ℝ :=
  if k ∈ E then 0 else
    Real.logb 2 (Fintype.card Out) -
      condEntropy (candidates E X ξ) (fun ξ' => ξ'.2 k) (fun ξ' => (ξ'.1, outputsBefore ξ'.2 k))

namespace InfoAux

section General

variable {Ω : Type*}

/-- Sum over `ω ∈ C` of the log-size of the class of `ω` for the relation `R`. -/
noncomputable def lsum (C : Finset Ω) (R : Ω → Ω → Prop) : ℝ :=
  ∑ ω ∈ C, Real.logb 2 ((C.filter fun ω' => R ω ω').card : ℝ)

lemma lsum_congr (C : Finset Ω) {R R' : Ω → Ω → Prop}
    (h : ∀ ω ∈ C, ∀ ω' ∈ C, (R ω ω' ↔ R' ω ω')) : lsum C R = lsum C R' := by
  unfold lsum
  refine Finset.sum_congr rfl fun ω hω => ?_
  rw [Finset.filter_congr fun ω' hω' => h ω hω ω' hω']

lemma condEntropy_eq_lsum {α β : Type*} (C : Finset Ω) (U : Ω → α) (V : Ω → β) :
    condEntropy C U V = (1 / (C.card : ℝ)) *
      (lsum C (fun ω ω' => V ω' = V ω) - lsum C (fun ω ω' => U ω' = U ω ∧ V ω' = V ω)) := by
  unfold condEntropy lsum
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ω hω => ?_
  have h1 : (0:ℝ) < ((C.filter fun ω' => V ω' = V ω).card : ℝ) := by
    exact_mod_cast Finset.card_pos.2 ⟨ω, by simp [hω]⟩
  have h2 : (0:ℝ) < ((C.filter fun ω' => U ω' = U ω ∧ V ω' = V ω).card : ℝ) := by
    exact_mod_cast Finset.card_pos.2 ⟨ω, by simp [hω]⟩
  rw [Real.logb_div h1.ne' h2.ne']
  congr

end General

section Records

variable {Z Out : Type*} {n : ℕ}

/-- Agreement on the secret part and on the outputs with index below `j`. -/
def rel (j : ℕ) (ξ ξ' : Z × (Fin n → Out)) : Prop :=
  ξ'.1 = ξ.1 ∧ ∀ i : Fin n, (i : ℕ) < j → ξ'.2 i = ξ.2 i

lemma outputsBefore_eq_iff (y y' : Fin n → Out) (k : Fin n) :
    outputsBefore y' k = outputsBefore y k ↔ ∀ i : Fin n, (i : ℕ) < k → y' i = y i := by
  simp only [outputsBefore, funext_iff]
  refine forall_congr' fun i => ?_
  by_cases h : i < k
  · have h' : (i : ℕ) < k := h
    simp [h, h']
  · have h' : ¬ (i : ℕ) < k := h
    simp [h, h']

lemma pair_iff (k : Fin n) (ξ ξ' : Z × (Fin n → Out)) :
    ((ξ'.1, outputsBefore ξ'.2 k) = (ξ.1, outputsBefore ξ.2 k)) ↔ rel k ξ ξ' := by
  rw [Prod.mk.injEq, outputsBefore_eq_iff]
  rfl

lemma rel_succ_iff (k : Fin n) (ξ ξ' : Z × (Fin n → Out)) :
    rel ((k : ℕ) + 1) ξ ξ' ↔ ξ'.2 k = ξ.2 k ∧ rel k ξ ξ' := by
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h2 k (Nat.lt_succ_self _), h1, fun i hi => h2 i (Nat.lt_succ_of_lt hi)⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h2, fun i hi => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | h
    · exact h3 i h
    · have : i = k := Fin.ext h
      subst this
      exact h1

lemma condEntropy_step (C : Finset (Z × (Fin n → Out))) (k : Fin n) :
    condEntropy C (fun ξ' => ξ'.2 k) (fun ξ' => (ξ'.1, outputsBefore ξ'.2 k)) =
      (1 / (C.card : ℝ)) * (lsum C (rel k) - lsum C (rel ((k : ℕ) + 1))) := by
  rw [condEntropy_eq_lsum]
  congr 2
  · exact lsum_congr C fun ξ _ ξ' _ => pair_iff k ξ ξ'
  · exact lsum_congr C fun ξ _ ξ' _ => by rw [rel_succ_iff, pair_iff]

lemma lsum_rel_top (C : Finset (Z × (Fin n → Out))) : lsum C (rel n) = 0 := by
  rw [lsum_congr C (R' := fun ξ ξ' => ξ' = ξ) (fun ξ _ ξ' _ => ?_)]
  · unfold lsum
    refine Finset.sum_eq_zero fun ξ hξ => ?_
    beta_reduce
    rw [Finset.card_eq_one.2 ⟨ξ, ?_⟩]
    · simp
    · ext ξ'
      simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · exact fun h => h.2
      · rintro rfl; exact ⟨hξ, rfl⟩
  · unfold rel
    constructor
    · rintro ⟨h1, h2⟩
      exact Prod.ext h1 (funext fun i => h2 i i.2)
    · rintro rfl
      exact ⟨rfl, fun _ _ => rfl⟩

lemma lsum_rel_zero (C : Finset (Z × (Fin n → Out))) :
    lsum C (rel 0) = lsum C (fun ξ ξ' => ξ'.1 = ξ.1) :=
  lsum_congr C fun ξ _ ξ' _ => by simp [rel]

lemma lsum_fst_ge [Fintype Z] [Nonempty Z] {Y : Type*} (C : Finset (Z × Y)) (hC : C.Nonempty) :
    (C.card : ℝ) * (Real.logb 2 C.card - Real.logb 2 (Fintype.card Z)) ≤
      lsum C (fun ξ ξ' => ξ'.1 = ξ.1) := by
  set c : Z → ℝ := fun z => ((C.filter fun ξ' => ξ'.1 = z).card : ℝ) with hc
  have h1 : lsum C (fun ξ ξ' => ξ'.1 = ξ.1) = ∑ z, c z * Real.logb 2 (c z) := by
    unfold lsum
    rw [← Finset.sum_fiberwise C Prod.fst]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [Finset.sum_congr rfl (g := fun _ => Real.logb 2 (c z)) ?_]
    · simp [c]
    · intro ξ hξ
      rw [Finset.mem_filter] at hξ
      simp [c, hξ.2]
  have h2 : ∑ z, c z = C.card := by
    simp only [c]
    exact_mod_cast (Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (t := Finset.univ)
      (fun _ _ => Finset.mem_univ _)).symm
  have hZ : (0:ℝ) < Fintype.card Z := by exact_mod_cast Fintype.card_pos
  have hCpos : (0:ℝ) < C.card := by exact_mod_cast hC.card_pos
  have hJ := Real.convexOn_mul_log.map_sum_le (t := Finset.univ)
    (w := fun _ => 1 / (Fintype.card Z : ℝ)) (p := c) (fun _ _ => by positivity)
    (by simp) (fun z _ => Set.mem_Ici.2 (by positivity))
  simp only [smul_eq_mul] at hJ
  rw [← Finset.mul_sum, ← Finset.mul_sum, h2] at hJ
  have key : (C.card : ℝ) * (Real.log C.card - Real.log (Fintype.card Z)) ≤
      ∑ z, c z * Real.log (c z) := by
    have e : 1 / (Fintype.card Z : ℝ) * C.card = C.card / Fintype.card Z := by ring
    rw [e, Real.log_div hCpos.ne' hZ.ne'] at hJ
    have := mul_le_mul_of_nonneg_left hJ hZ.le
    have e2 : (Fintype.card Z : ℝ) * (C.card / Fintype.card Z *
        (Real.log C.card - Real.log (Fintype.card Z))) =
        C.card * (Real.log C.card - Real.log (Fintype.card Z)) := by
      field_simp
    have e3 : (Fintype.card Z : ℝ) * (1 / Fintype.card Z * ∑ z, c z * Real.log (c z)) =
        ∑ z, c z * Real.log (c z) := by
      field_simp
    linarith
  rw [h1]
  have hl2 : (0:ℝ) < Real.log 2 := Real.log_pos one_lt_two
  have e4 : ∑ z, c z * Real.logb 2 (c z) = (∑ z, c z * Real.log (c z)) / Real.log 2 := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [Real.logb, mul_div_assoc]
  rw [e4, Real.logb, Real.logb, ← sub_div, ← mul_div_assoc]
  exact div_le_div_of_nonneg_right key hl2.le

end Records

lemma sum_infoWeight_le {Z Obs Out : Type*} [Fintype Z] [Fintype Out] [Nonempty Z] {n : ℕ}
    (E : Finset (Fin n)) (X : Z × (Fin n → Out) → Obs) (ξ : Z × (Fin n → Out)) :
    ∑ k, infoWeight E X ξ k ≤
      ((Finset.univ.filter fun k => k ∉ E).card : ℝ) * Real.logb 2 (Fintype.card Out) -
        Real.logb 2 (candidates E X ξ).card + Real.logb 2 (Fintype.card Z) := by
  set C := candidates E X ξ with hCdef
  have hξC : ξ ∈ C := by simp [C, candidates]
  have hCpos : (0:ℝ) < C.card := by exact_mod_cast Finset.card_pos.2 ⟨ξ, hξC⟩
  have hw : ∀ k, infoWeight E X ξ k =
      (if k ∈ E then 0 else Real.logb 2 (Fintype.card Out)) -
        (1 / (C.card : ℝ)) * (lsum C (rel k) - lsum C (rel ((k : ℕ) + 1))) := by
    intro k
    unfold infoWeight
    split_ifs with hk
    · have : lsum C (rel k) = lsum C (rel ((k : ℕ) + 1)) := lsum_congr C fun ω hω ω' hω' => by
        rw [rel_succ_iff]
        simp only [C, candidates, Finset.mem_filter, Finset.mem_univ, true_and] at hω hω'
        exact ⟨fun h => ⟨(hω'.2 k hk).trans (hω.2 k hk).symm, h⟩, fun h => h.2⟩
      rw [this]
      simp
    · rw [condEntropy_step]
  rw [Finset.sum_congr rfl fun k _ => hw k, Finset.sum_sub_distrib, ← Finset.mul_sum]
  have tele : ∑ k : Fin n, (lsum C (rel (k : ℕ)) - lsum C (rel ((k : ℕ) + 1))) =
      lsum C (rel 0) - lsum C (rel n) := by
    rw [Fin.sum_univ_eq_sum_range (fun i => lsum C (rel i) - lsum C (rel (i + 1))) n,
      Finset.sum_range_sub']
  rw [tele, lsum_rel_top, lsum_rel_zero, Finset.sum_ite, Finset.sum_const_zero, zero_add,
    Finset.sum_const, nsmul_eq_mul]
  have J := lsum_fst_ge C ⟨ξ, hξC⟩
  have J2 : Real.logb 2 C.card - Real.logb 2 (Fintype.card Z) ≤
      1 / (C.card : ℝ) * (lsum C (fun ξ ξ' => ξ'.1 = ξ.1) - 0) := by
    rw [sub_zero, one_div_mul_eq_div, le_div_iff₀ hCpos]
    linarith
  linarith

end InfoAux

open InfoAux in
/-- The information bound (Lemma 2 of the paper). -/
theorem card_infoWeight_gt_le {Z Obs Out : Type*} [Fintype Z] [Fintype Obs] [Fintype Out]
    [Nonempty Z] [Nonempty Out] {n : ℕ} (E : Finset (Fin n)) (X : Z × (Fin n → Out) → Obs)
    (ℓ : ℕ) (hObs : Fintype.card Obs ≤ 2 ^ ℓ) (u : ℝ) (hu : 0 ≤ u) :
    ((Finset.univ.filter fun ξ => (ℓ : ℝ) + u < ∑ k, infoWeight E X ξ k).card : ℝ) /
        (Fintype.card (Z × (Fin n → Out)) : ℝ) ≤ (2 : ℝ) ^ (-u) := by
  clear hu
  set K := Fintype.card Out with hK
  set m := (Finset.univ.filter fun k : Fin n => k ∉ E).card with hmdef
  have hm : E.card + m = n := by
    have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
      (fun k : Fin n => k ∈ E)
    simpa using this
  have hZpos : (0:ℝ) < Fintype.card Z := by exact_mod_cast Fintype.card_pos
  have hKpos : (0:ℝ) < K := by exact_mod_cast Fintype.card_pos
  set N : ℝ := (Fintype.card Z : ℝ) * (K : ℝ) ^ m with hN
  set T : ℝ := N / (2 : ℝ) ^ ((ℓ : ℝ) + u) with hT
  have hTnn : 0 ≤ T := by positivity
  have hbad : ∀ ξ, (ℓ : ℝ) + u < ∑ k, infoWeight E X ξ k →
      ((candidates E X ξ).card : ℝ) < T := by
    intro ξ h
    have hle := sum_infoWeight_le E X ξ
    have hξC : ξ ∈ candidates E X ξ := by simp [candidates]
    have hCpos : (0:ℝ) < (candidates E X ξ).card := by
      exact_mod_cast Finset.card_pos.2 ⟨ξ, hξC⟩
    have e : Real.logb 2 (N / (candidates E X ξ).card) =
        m * Real.logb 2 K - Real.logb 2 (candidates E X ξ).card +
          Real.logb 2 (Fintype.card Z) := by
      rw [Real.logb_div (by positivity) hCpos.ne', Real.logb_mul (by positivity) (by positivity),
        Real.logb_pow]
      ring
    have h2 : (ℓ : ℝ) + u < Real.logb 2 (N / (candidates E X ξ).card) := by
      rw [e]; linarith
    rw [Real.lt_logb_iff_rpow_lt one_lt_two (by positivity), lt_div_iff₀ hCpos] at h2
    rw [hT, lt_div_iff₀ (by positivity)]
    linarith
  set S := Finset.univ.filter fun ξ => (ℓ : ℝ) + u < ∑ k, infoWeight E X ξ k with hS
  let key : Z × (Fin n → Out) → Obs × (E → Out) := fun ξ => (X ξ, fun k => ξ.2 k)
  have hScard : (S.card : ℝ) ≤ (Fintype.card (Obs × (E → Out)) : ℝ) * T := by
    rw [Finset.card_eq_sum_card_fiberwise (f := key) (t := Finset.univ)
      (fun _ _ => Finset.mem_univ _)]
    push_cast
    calc ∑ p, ((S.filter fun ξ => key ξ = p).card : ℝ)
        ≤ ∑ _p : Obs × (E → Out), T := Finset.sum_le_sum fun p _ => ?_
      _ = _ := by simp
    rcases (S.filter fun ξ => key ξ = p).eq_empty_or_nonempty with h | ⟨ξ₀, hξ₀⟩
    · rw [h]; simpa using hTnn
    · have hsub : (S.filter fun ξ => key ξ = p) ⊆ candidates E X ξ₀ := by
        intro ξ hξ
        have hξ' := (Finset.mem_filter.1 hξ).2
        have e : key ξ = key ξ₀ := hξ'.trans (Finset.mem_filter.1 hξ₀).2.symm
        simp only [candidates, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨congrArg Prod.fst e, fun k hk => congrFun (congrArg Prod.snd e) ⟨k, hk⟩⟩
      have hb := hbad ξ₀ (by simpa [S] using (Finset.mem_filter.1 hξ₀).1)
      exact le_trans (by exact_mod_cast Finset.card_le_card hsub) hb.le
  have hcard1 : (Fintype.card (Z × (Fin n → Out)) : ℝ) = Fintype.card Z * (K : ℝ) ^ n := by
    simp [K, Fintype.card_prod]
  have hcard2 : (Fintype.card (Obs × (E → Out)) : ℝ) = Fintype.card Obs * (K : ℝ) ^ E.card := by
    simp [K, Fintype.card_prod]
  have hObs' : (Fintype.card Obs : ℝ) ≤ 2 ^ ℓ := by exact_mod_cast hObs
  have hpow : (K : ℝ) ^ E.card * (K : ℝ) ^ m = (K : ℝ) ^ n := by
    rw [← pow_add, hm]
  have h2u : (2 : ℝ) ^ ((ℓ : ℝ) + u) = 2 ^ ℓ * (2 : ℝ) ^ u := by
    rw [Real.rpow_add two_pos, Real.rpow_natCast]
  have h2u' : (0:ℝ) < (2 : ℝ) ^ u := by positivity
  rw [hcard1, div_le_iff₀ (by positivity), Real.rpow_neg zero_le_two]
  calc (S.card : ℝ) ≤ Fintype.card Obs * (K : ℝ) ^ E.card * T := by rw [← hcard2]; exact hScard
    _ ≤ 2 ^ ℓ * (K : ℝ) ^ E.card * T := by gcongr
    _ = ((2 : ℝ) ^ u)⁻¹ * (Fintype.card Z * (K : ℝ) ^ n) := by
      rw [hT, hN, h2u, ← hpow]
      field_simp

end OptimalOTS
