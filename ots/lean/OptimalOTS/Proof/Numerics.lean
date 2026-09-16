import OptimalOTS.Proof.NumericsDefs

/-!
# Numerical bounds (Appendix B of the paper)
-/

namespace OptimalOTS.Numerics

theorem hundred_lt_countingFactor : 100 < (2 : ℝ) ^ 115 * countingFactor 22 5257 123 := by
  unfold countingFactor
  simp only [Finset.prod_range_succ, Finset.prod_range_zero]
  norm_num

private lemma prod_strictAntiOn (g : ℕ → ℝ → ℝ)
    (hpos : ∀ k d, 0 < d → 0 < g k d)
    (hanti : ∀ k, StrictAntiOn (g k) (Set.Ioi 0)) (n : ℕ) :
    StrictAntiOn (fun d => ∏ k ∈ Finset.range (n + 1), g k d) (Set.Ioi 0) := by
  induction n with
  | zero => simpa using hanti 0
  | succ n ih =>
    intro x hx y hy hxy
    simp only [Finset.prod_range_succ (n := n + 1)]
    have h1 := ih hx hy hxy
    have h2 := hanti (n + 1) hx hy hxy
    have hp : 0 < ∏ k ∈ Finset.range (n + 1), g k y :=
      Finset.prod_pos fun k _ => hpos k y hy
    have hgx := hpos (n + 1) x hx
    exact mul_lt_mul'' h1 h2 hp.le (hpos (n + 1) y hy).le

theorem countingFactor_div_pow_strictAntiOn :
    StrictAntiOn (fun d : ℝ => countingFactor 22 5257 d / d ^ 22) (Set.Ioi 0) := by
  set g : ℕ → ℝ → ℝ := fun k d =>
    (21 * 5257 / (5257 + d) + ((k : ℝ) + 1)) / (22 * 5257 + ((k : ℝ) + 1) * d) with hg
  have hpos : ∀ k d, 0 < d → 0 < g k d := by
    intro k d hd; simp only [hg]; positivity
  have hanti : ∀ k, StrictAntiOn (g k) (Set.Ioi 0) := by
    intro k x hx y hy hxy
    simp only [Set.mem_Ioi] at hx hy
    simp only [hg]
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hnum : 21 * 5257 / (5257 + y) + ((k : ℝ) + 1) ≤ 21 * 5257 / (5257 + x) + ((k : ℝ) + 1) := by
      gcongr
    have hden : 22 * 5257 + ((k : ℝ) + 1) * x < 22 * 5257 + ((k : ℝ) + 1) * y := by
      nlinarith
    calc (21 * 5257 / (5257 + y) + ((k : ℝ) + 1)) / (22 * 5257 + ((k : ℝ) + 1) * y)
        ≤ (21 * 5257 / (5257 + x) + ((k : ℝ) + 1)) / (22 * 5257 + ((k : ℝ) + 1) * y) := by
          gcongr
      _ < (21 * 5257 / (5257 + x) + ((k : ℝ) + 1)) / (22 * 5257 + ((k : ℝ) + 1) * x) := by
          apply div_lt_div_of_pos_left (by positivity) (by positivity) hden
  have heq : Set.EqOn (fun d : ℝ => countingFactor 22 5257 d / d ^ 22)
      (fun d => ∏ k ∈ Finset.range (21 + 1), g k d) (Set.Ioi 0) := by
    intro d hd
    simp only [Set.mem_Ioi] at hd
    simp only [countingFactor]
    rw [show d ^ 22 = ∏ k ∈ Finset.range (21 + 1), d by simp, ← Finset.prod_div_distrib]
    apply Finset.prod_congr rfl
    intro k _
    simp only [hg]
    push_cast
    have hd' : d ≠ 0 := hd.ne'
    have h1 : 5257 + d ≠ 0 := by positivity
    field_simp
    ring
  exact (prod_strictAntiOn g hpos hanti 21).congr heq.symm

theorem budget_lt_logb : 123 < Real.logb 2 (Real.exp 1 * q * Real.log q) := by
  have he := Real.exp_one_gt_d9
  have hl := Real.log_two_gt_d9
  have hq' : (q : ℝ) = 5 * 2 ^ 113 := by unfold q; push_cast; ring
  have hq : Real.log (q : ℝ) = Real.log 5 + 113 * Real.log 2 := by
    rw [hq', Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    norm_num
  have h5 : 0 < Real.log 5 := Real.log_pos (by norm_num)
  have hlq : 78 < Real.log (q : ℝ) := by rw [hq]; nlinarith
  have hqpos : (0 : ℝ) < q := by unfold q; positivity
  rw [Real.lt_logb_iff_rpow_lt (by norm_num) (by positivity)]
  have : (2 : ℝ) ^ (123 : ℝ) = 2 ^ (123 : ℕ) := by norm_cast
  rw [this]
  rw [hq']
  rw [hq'] at hlq
  have h1 : (2:ℝ)^123 = 1024 * 2^113 := by norm_num
  rw [h1]
  have h2 : (0:ℝ) < 2^113 := by positivity
  have h3 : (1024 : ℝ) < Real.exp 1 * 5 * Real.log (5 * 2 ^ 113) := by nlinarith
  nlinarith

theorem signFailure_lt : signFailure < (2 : ℝ)⁻¹ ^ 256 := by
  unfold signFailure
  have h1 : 1 - (2 : ℝ)⁻¹ ^ 13 ≤ Real.exp (-((2 : ℝ)⁻¹ ^ 13)) := by
    have := Real.add_one_le_exp (-((2 : ℝ)⁻¹ ^ 13)); linarith
  have h0 : 0 ≤ 1 - (2 : ℝ)⁻¹ ^ 13 := by norm_num
  calc (1 - (2 : ℝ)⁻¹ ^ 13) ^ (2 ^ 21) ≤ Real.exp (-((2 : ℝ)⁻¹ ^ 13)) ^ (2 ^ 21) :=
        pow_le_pow_left₀ h0 h1 _
    _ = Real.exp (-1) ^ 256 := by
        rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]; congr 1; norm_num
    _ < (1 / 2) ^ 256 := by
        exact pow_lt_pow_left₀ Real.exp_neg_one_lt_half (Real.exp_pos _).le (by norm_num)
    _ = (2 : ℝ)⁻¹ ^ 256 := by norm_num

theorem attackCost_div_lt : (attackCost : ℝ) / 2 ^ 127 < 27 / 500 := by
  unfold attackCost T q
  norm_num

end OptimalOTS.Numerics
