import Submissions.Lower.Entropy

/-!
# Basic properties of `condEntropy`
-/

open scoped Classical

namespace OptimalOTS

variable {Ω α β γ : Type*}

/-- Double-counting bound: for finsets `S`, `T` and a function `g`,
`∑_{x ∈ T} #{y ∈ S | g y = g x} / #{y ∈ T | g y = g x} ≤ #S`. -/
private lemma sum_card_div_card_le (S T : Finset Ω) (g : Ω → α) :
    ∑ x ∈ T, ((S.filter fun y => g y = g x).card : ℝ) /
      ((T.filter fun y => g y = g x).card : ℝ) ≤ S.card := by
  have h1 : ∀ x ∈ T, ((S.filter fun y => g y = g x).card : ℝ) /
      ((T.filter fun y => g y = g x).card : ℝ)
      = ∑ y ∈ S, if g y = g x then 1 / ((T.filter fun z => g z = g y).card : ℝ) else 0 := by
    intro x _
    rw [Finset.card_filter, Nat.cast_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun y _ => ?_
    split_ifs with h
    · simp [h]
    · simp
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  calc ∑ y ∈ S, ∑ x ∈ T,
        (if g y = g x then 1 / ((T.filter fun z => g z = g y).card : ℝ) else 0)
      ≤ ∑ y ∈ S, (1 : ℝ) := by
        refine Finset.sum_le_sum fun y _ => ?_
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
        have : (T.filter fun x => g y = g x) = T.filter fun z => g z = g y := by
          ext; simp [eq_comm]
        rw [this, mul_one_div]
        exact div_self_le_one _
    _ = S.card := by simp

private lemma condEntropy_eq (C : Finset Ω) (U : Ω → α) (V : Ω → β) :
    condEntropy C U V = (1 / (C.card : ℝ)) *
      (∑ ω ∈ C, Real.log (((C.filter fun ω' => V ω' = V ω).card : ℝ) /
        ((C.filter fun ω' => U ω' = U ω ∧ V ω' = V ω).card : ℝ))) / Real.log 2 := by
  unfold condEntropy
  simp only [Real.logb, ← Finset.sum_div, ← Finset.mul_sum, mul_div_assoc]

private lemma card_filter_pos (C : Finset Ω) (U : Ω → α) (V : Ω → β) {ω : Ω} (hω : ω ∈ C) :
    (0 : ℝ) < ((C.filter fun ω' => U ω' = U ω ∧ V ω' = V ω).card : ℝ) := by
  exact_mod_cast Finset.card_pos.mpr ⟨ω, by simp [hω]⟩

private lemma card_filter_pos' (C : Finset Ω) (V : Ω → β) {ω : Ω} (hω : ω ∈ C) :
    (0 : ℝ) < ((C.filter fun ω' => V ω' = V ω).card : ℝ) := by
  exact_mod_cast Finset.card_pos.mpr ⟨ω, by simp [hω]⟩

theorem condEntropy_nonneg (C : Finset Ω) (U : Ω → α) (V : Ω → β) :
    0 ≤ condEntropy C U V := by
  unfold condEntropy
  refine Finset.sum_nonneg fun ω hω =>
    mul_nonneg (by positivity) (Real.logb_nonneg (by norm_num) ?_)
  rw [le_div_iff₀ (card_filter_pos C U V hω), one_mul]
  exact_mod_cast Finset.card_le_card (fun x hx => by simp at hx ⊢; tauto)

/-- Entropy is at most the logarithm of the number of values. -/
theorem condEntropy_le_logb_card [Fintype α] (C : Finset Ω) (U : Ω → α) (V : Ω → β) :
    condEntropy C U V ≤ Real.logb 2 (Fintype.card α) := by
  rcases C.eq_empty_or_nonempty with rfl | ⟨ω₀, hω₀⟩
  · simp only [condEntropy, Finset.sum_empty]
    exact div_nonneg (Real.log_natCast_nonneg _) (Real.log_nonneg (by norm_num))
  have hk : (0 : ℝ) < Fintype.card α := by
    exact_mod_cast Fintype.card_pos_iff.mpr ⟨U ω₀⟩
  have hn : (0 : ℝ) < C.card := by exact_mod_cast Finset.card_pos.mpr ⟨ω₀, hω₀⟩
  set k : ℝ := (Fintype.card α : ℝ) with hk_def
  -- The combinatorial bound.
  have hab : ∑ ω ∈ C, ((C.filter fun ω' => V ω' = V ω).card : ℝ) /
      ((C.filter fun ω' => U ω' = U ω ∧ V ω' = V ω).card : ℝ) ≤ k * C.card := by
    rw [← Finset.sum_fiberwise C U]
    calc ∑ u, ∑ ω ∈ C with U ω = u, ((C.filter fun ω' => V ω' = V ω).card : ℝ) /
          ((C.filter fun ω' => U ω' = U ω ∧ V ω' = V ω).card : ℝ)
        = ∑ u, ∑ ω ∈ C.filter (fun ω => U ω = u),
            ((C.filter fun y => V y = V ω).card : ℝ) /
            (((C.filter (fun ω => U ω = u)).filter fun y => V y = V ω).card : ℝ) := by
          refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun ω hω => ?_
          rw [Finset.mem_filter] at hω
          rw [Finset.filter_filter]
          congr 3
          ext y
          simp only [Finset.mem_filter, hω.2]
      _ ≤ ∑ _u : α, (C.card : ℝ) :=
          Finset.sum_le_sum fun u _ => sum_card_div_card_le _ _ _
      _ = k * C.card := by simp [k]
  have hsum : ∑ ω ∈ C, Real.log (((C.filter fun ω' => V ω' = V ω).card : ℝ) /
      ((C.filter fun ω' => U ω' = U ω ∧ V ω' = V ω).card : ℝ)) ≤ C.card * Real.log k := by
    have h1 : ∀ ω ∈ C, Real.log (((C.filter fun ω' => V ω' = V ω).card : ℝ) /
        ((C.filter fun ω' => U ω' = U ω ∧ V ω' = V ω).card : ℝ)) - Real.log k ≤
        (((C.filter fun ω' => V ω' = V ω).card : ℝ) /
        ((C.filter fun ω' => U ω' = U ω ∧ V ω' = V ω).card : ℝ)) / k - 1 := by
      intro ω hω
      have hpos : 0 < ((C.filter fun ω' => V ω' = V ω).card : ℝ) /
          ((C.filter fun ω' => U ω' = U ω ∧ V ω' = V ω).card : ℝ) :=
        div_pos (card_filter_pos' C V hω) (card_filter_pos C U V hω)
      rw [← Real.log_div hpos.ne' hk.ne']
      exact Real.log_le_sub_one_of_pos (div_pos hpos hk)
    have h2 := Finset.sum_le_sum h1
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.sum_div] at h2
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at h2
    have h3 : (∑ ω ∈ C, ((C.filter fun ω' => V ω' = V ω).card : ℝ) /
        ((C.filter fun ω' => U ω' = U ω ∧ V ω' = V ω).card : ℝ)) / k ≤ C.card := by
      rw [div_le_iff₀ hk]; linarith
    linarith
  rw [condEntropy_eq, Real.logb, div_le_div_iff_of_pos_right (Real.log_pos one_lt_two),
    one_div, inv_mul_le_iff₀ hn]
  exact hsum

/-- Conditioning on more information cannot increase entropy: if `V` is a function of `V'` on
`C`, then `H(U | V') ≤ H(U | V)`. -/
theorem condEntropy_le_of_factor (C : Finset Ω) (U : Ω → α) (V : Ω → β) (V' : Ω → γ)
    (f : γ → β) (hf : ∀ ω ∈ C, V ω = f (V' ω)) :
    condEntropy C U V' ≤ condEntropy C U V := by
  -- The combinatorial bound.
  have hab : ∑ ω ∈ C, (((C.filter fun ω' => V' ω' = V' ω).card : ℝ) /
      ((C.filter fun ω' => U ω' = U ω ∧ V' ω' = V' ω).card : ℝ)) /
      (((C.filter fun ω' => V ω' = V ω).card : ℝ) /
      ((C.filter fun ω' => U ω' = U ω ∧ V ω' = V ω).card : ℝ)) ≤ C.card := by
    rw [← Finset.sum_fiberwise_of_maps_to (t := C.image V')
      (fun ω hω => Finset.mem_image_of_mem V' hω)]
    have hcard : (C.card : ℝ) = ∑ v ∈ C.image V', ((C.filter fun ω => V' ω = v).card : ℝ) := by
      exact_mod_cast Finset.card_eq_sum_card_image V' C
    rw [hcard]
    refine Finset.sum_le_sum fun v _ => ?_
    set T := C.filter fun ω => V' ω = v with hT
    set S := C.filter fun ω => V ω = f v with hS
    calc ∑ ω ∈ C with V' ω = v, (((C.filter fun ω' => V' ω' = V' ω).card : ℝ) /
          ((C.filter fun ω' => U ω' = U ω ∧ V' ω' = V' ω).card : ℝ)) /
          (((C.filter fun ω' => V ω' = V ω).card : ℝ) /
          ((C.filter fun ω' => U ω' = U ω ∧ V ω' = V ω).card : ℝ))
        = ∑ ω ∈ T, ((T.card : ℝ) / S.card) *
            (((S.filter fun y => U y = U ω).card : ℝ) /
              ((T.filter fun y => U y = U ω).card : ℝ)) := by
          refine Finset.sum_congr rfl fun ω hω => ?_
          rw [Finset.mem_filter] at hω
          have hVω : V ω = f v := by rw [hf ω hω.1, hω.2]
          have e1 : (C.filter fun ω' => V' ω' = V' ω) = T := by
            rw [hT, hω.2]
          have e2 : (C.filter fun ω' => U ω' = U ω ∧ V' ω' = V' ω) =
              T.filter fun y => U y = U ω := by
            ext y; simp only [hT, Finset.mem_filter, hω.2]; tauto
          have e3 : (C.filter fun ω' => V ω' = V ω) = S := by
            rw [hS, hVω]
          have e4 : (C.filter fun ω' => U ω' = U ω ∧ V ω' = V ω) =
              S.filter fun y => U y = U ω := by
            ext y; simp only [hS, Finset.mem_filter, hVω]; tauto
          rw [e1, e2, e3, e4]; simp only [div_eq_mul_inv, mul_inv, inv_inv]
          ring
      _ = ((T.card : ℝ) / S.card) * ∑ ω ∈ T,
            (((S.filter fun y => U y = U ω).card : ℝ) /
              ((T.filter fun y => U y = U ω).card : ℝ)) := by
          rw [Finset.mul_sum]
      _ ≤ ((T.card : ℝ) / S.card) * S.card :=
          mul_le_mul_of_nonneg_left (sum_card_div_card_le S T U) (by positivity)
      _ ≤ T.card := by
          rcases eq_or_ne (S.card : ℝ) 0 with h | h
          · rw [h, mul_zero]; positivity
          · rw [div_mul_cancel₀ _ h]
  have hsum : ∑ ω ∈ C, Real.log (((C.filter fun ω' => V' ω' = V' ω).card : ℝ) /
      ((C.filter fun ω' => U ω' = U ω ∧ V' ω' = V' ω).card : ℝ)) ≤
      ∑ ω ∈ C, Real.log (((C.filter fun ω' => V ω' = V ω).card : ℝ) /
      ((C.filter fun ω' => U ω' = U ω ∧ V ω' = V ω).card : ℝ)) := by
    have h1 : ∀ ω ∈ C, Real.log (((C.filter fun ω' => V' ω' = V' ω).card : ℝ) /
        ((C.filter fun ω' => U ω' = U ω ∧ V' ω' = V' ω).card : ℝ)) -
        Real.log (((C.filter fun ω' => V ω' = V ω).card : ℝ) /
        ((C.filter fun ω' => U ω' = U ω ∧ V ω' = V ω).card : ℝ)) ≤
        (((C.filter fun ω' => V' ω' = V' ω).card : ℝ) /
        ((C.filter fun ω' => U ω' = U ω ∧ V' ω' = V' ω).card : ℝ)) /
        (((C.filter fun ω' => V ω' = V ω).card : ℝ) /
        ((C.filter fun ω' => U ω' = U ω ∧ V ω' = V ω).card : ℝ)) - 1 := by
      intro ω hω
      have hpos : 0 < ((C.filter fun ω' => V ω' = V ω).card : ℝ) /
          ((C.filter fun ω' => U ω' = U ω ∧ V ω' = V ω).card : ℝ) :=
        div_pos (card_filter_pos' C V hω) (card_filter_pos C U V hω)
      have hpos' : 0 < ((C.filter fun ω' => V' ω' = V' ω).card : ℝ) /
          ((C.filter fun ω' => U ω' = U ω ∧ V' ω' = V' ω).card : ℝ) :=
        div_pos (card_filter_pos' C V' hω) (card_filter_pos C U V' hω)
      rw [← Real.log_div hpos'.ne' hpos.ne']
      exact Real.log_le_sub_one_of_pos (div_pos hpos' hpos)
    have h2 := Finset.sum_le_sum h1
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib] at h2
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at h2
    linarith
  rw [condEntropy_eq, condEntropy_eq]
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hsum (by positivity)) (Real.log_nonneg (by norm_num))

end OptimalOTS
