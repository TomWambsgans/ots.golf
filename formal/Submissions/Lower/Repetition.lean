import Mathlib

/-!
# Success after repeated attempts

If independent attempts each succeed with probability `p`, all `q` of them fail with probability
`(1 - p) ^ q`. The estimate below bounds this by `-ln p / (ln q + ln ln q + 1)`; averaged over the
oracle it turns a bound on `E[-log p]` into a bound on the failure probability of `q` attempts.
-/

namespace OptimalOTS

/-- `e * x ≤ exp x`. -/
private lemma rep_exp_ge (x : ℝ) : Real.exp 1 * x ≤ Real.exp x := by
  have h := Real.add_one_le_exp (x - 1)
  have hx : Real.exp x = Real.exp 1 * Real.exp (x - 1) := by
    rw [← Real.exp_add]; ring_nf
  rw [hx]
  have he := Real.exp_pos 1
  nlinarith

/-- The repetition estimate in the variable `u = -ln p`, without division. -/
private lemma rep_key (q : ℕ) (hq : 3 ≤ q) (u : ℝ) (hu : 0 ≤ u) :
    (Real.log q + Real.log (Real.log q) + 1) * (1 - Real.exp (-u)) ^ q ≤ u := by
  have hq3 : (3:ℝ) ≤ q := by exact_mod_cast hq
  have hqpos : (0:ℝ) < q := by linarith
  set lq := Real.log q with hlq_def
  have he : (2.7182818283:ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have he' : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have hlq1 : 1 < lq := by
    rw [Real.lt_log_iff_exp_lt hqpos]; linarith
  have hlqpos : 0 < lq := by linarith
  have hexp_lq : Real.exp lq = q := Real.exp_log hqpos
  have hllq : Real.log lq ≤ lq - 1 := Real.log_le_sub_one_of_pos hlqpos
  have hllq0 : 0 ≤ Real.log lq := Real.log_nonneg hlq1.le
  set L := lq + Real.log lq + 1 with hL_def
  have hL2 : L ≤ 2 * lq := by linarith
  have hlq38 : lq ≤ 3 * q / 8 := by
    have := rep_exp_ge lq
    rw [hexp_lq] at this
    nlinarith
  have hLq : L ≤ 3 * q / 4 := by linarith
  have hLpos : 0 < L := by linarith
  set p := Real.exp (-u) with hp_def
  have hp0 : 0 < p := Real.exp_pos _
  have hp1 : p ≤ 1 := by rw [hp_def]; exact Real.exp_le_one_iff.mpr (by linarith)
  have h1p : 1 - p ≤ u := by have := Real.add_one_le_exp (-u); linarith
  have hexpb : (1 - p) ^ q ≤ Real.exp (-(q * p)) := by
    have h : 1 - p ≤ Real.exp (-p) := by have := Real.add_one_le_exp (-p); linarith
    calc (1 - p) ^ q ≤ Real.exp (-p) ^ q := pow_le_pow_left₀ (by linarith) h q
      _ = Real.exp (-(q * p)) := by rw [← Real.exp_nat_mul]; ring_nf
  have hred : L ≤ u * Real.exp (q * p) → L * (1 - p) ^ q ≤ u := by
    intro h
    have hmul : Real.exp (q * p) * Real.exp (-(q * p)) = 1 := by
      rw [← Real.exp_add]; simp
    calc L * (1 - p) ^ q ≤ L * Real.exp (-(q * p)) :=
          mul_le_mul_of_nonneg_left hexpb hLpos.le
      _ ≤ u * Real.exp (q * p) * Real.exp (-(q * p)) :=
          mul_le_mul_of_nonneg_right h (Real.exp_pos _).le
      _ = u := by rw [mul_assoc, hmul, mul_one]
  have hqp : (q : ℝ) * p = Real.exp (lq - u) := by
    rw [Real.exp_sub, hexp_lq, hp_def, Real.exp_neg]; field_simp
  have hs0 : 0 ≤ (q : ℝ) * p := by positivity
  rcases le_or_gt L u with hA | hA
  · have h1 : (1 - p) ^ q ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
    nlinarith
  rcases le_or_gt lq u with hB | hB
  · apply hred
    have hs : L - u ≤ q * p * lq := by
      rw [hqp]
      have h2 : Real.exp (lq - u) * lq = Real.exp (lq + Real.log lq - u) := by
        rw [show lq + Real.log lq - u = (lq - u) + Real.log lq by ring, Real.exp_add,
          Real.exp_log hlqpos]
      rw [h2]
      have := Real.add_one_le_exp (lq + Real.log lq - u)
      linarith
    have h3 := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (q * p)) hu
    have h4 : 0 ≤ (q * p) * (u - lq) := mul_nonneg hs0 (by linarith)
    nlinarith
  have hC : Real.exp 1 * (u * (q * p)) ≤ u * Real.exp (q * p) := by
    have := mul_le_mul_of_nonneg_left (rep_exp_ge (q * p)) hu
    linarith
  rcases le_or_gt 1 u with hC1 | hC1
  · apply hred
    have h5 : lq ≤ u * (q * p) := by
      rw [hqp]
      have := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (lq - u)) hu
      nlinarith
    have h6 : Real.exp 1 * lq ≤ Real.exp 1 * (u * (q * p)) :=
      mul_le_mul_of_nonneg_left h5 (Real.exp_pos 1).le
    nlinarith
  rcases le_or_gt (1/2) u with hC2 | hC2
  · apply hred
    -- exp (u - 1/2) ≤ 2 u
    have hx : Real.exp (u - 1/2) ≤ 2 * u := by
      have h7 := Real.add_one_le_exp (-(u - 1/2))
      have h8 : Real.exp (u - 1/2) * Real.exp (-(u - 1/2)) = 1 := by
        rw [← Real.exp_add]; simp
      have h9 := Real.exp_pos (u - 1/2)
      have h10 : Real.exp (u - 1/2) * (1 - (u - 1/2)) ≤ 1 := by nlinarith
      nlinarith
    have h11 : Real.exp (-(1/2:ℝ)) = Real.exp (-u) * Real.exp (u - 1/2) := by
      rw [← Real.exp_add]; ring_nf
    have h12 : (1/2) * Real.exp (-(1/2:ℝ)) ≤ u * p := by
      rw [h11, ← hp_def]; nlinarith
    have h13 : Real.exp 1 * Real.exp (-(1/2:ℝ)) = Real.exp (1/2) := by
      rw [← Real.exp_add]; norm_num
    have h14 : (1/2:ℝ) + 1 ≤ Real.exp (1/2) := Real.add_one_le_exp _
    have h15 : Real.exp 1 * ((q:ℝ) * ((1/2) * Real.exp (-(1/2:ℝ)))) ≤
        Real.exp 1 * (u * (q * p)) := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos 1).le
      have := mul_le_mul_of_nonneg_left h12 hqpos.le
      linarith
    have h16 : Real.exp 1 * ((q:ℝ) * ((1/2) * Real.exp (-(1/2:ℝ)))) =
        q / 2 * Real.exp (1/2) := by
      rw [← h13]; ring
    have h17 := mul_le_mul_of_nonneg_left h14 hqpos.le
    linarith
  · -- small u
    obtain ⟨n, rfl⟩ : ∃ n, q = n + 1 := ⟨q - 1, by omega⟩
    have hpn : (1 - p) ^ n ≤ (1/2) ^ n := pow_le_pow_left₀ (by linarith) (by linarith) n
    have h2n : ((n:ℝ) + 1) ≤ 2 ^ n := by
      have := one_add_mul_le_pow (a := (1:ℝ)) (by norm_num) n
      norm_num at this; linarith
    have hhalf : (2:ℝ) ^ n * (1/2) ^ n = 1 := by rw [← mul_pow]; norm_num
    have hLn : L * (1 - p) ^ n ≤ 1 := by
      have hc : ((n + 1 : ℕ) : ℝ) = n + 1 := by push_cast; ring
      rw [hc] at hLq
      have h0 : 0 ≤ (1 - p) ^ n := pow_nonneg (by linarith) n
      have : L * (1 - p) ^ n ≤ 2 ^ n * (1/2) ^ n := by
        apply mul_le_mul (by linarith) hpn h0 (by positivity)
      linarith
    rw [pow_succ, ← mul_assoc]
    have h1p0 : 0 ≤ 1 - p := by linarith
    have := mul_le_mul_of_nonneg_right hLn h1p0
    linarith

/-- The repetition estimate (Lemma A.1 of the paper). -/
theorem one_sub_pow_le_neg_log_div (q : ℕ) (hq : 3 ≤ q) (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) :
    (1 - p) ^ q ≤ -Real.log p / (Real.log q + Real.log (Real.log q) + 1) := by
  have hq3 : (3:ℝ) ≤ q := by exact_mod_cast hq
  have hlq1 : 1 < Real.log q := by
    rw [Real.lt_log_iff_exp_lt (by linarith)]
    have := Real.exp_one_lt_d9; linarith
  have hL : 0 < Real.log q + Real.log (Real.log q) + 1 := by
    have := Real.log_nonneg hlq1.le; linarith
  have hu : 0 ≤ -Real.log p := by have := Real.log_nonpos hp.le hp1; linarith
  have hk := rep_key q hq (-Real.log p) hu
  rw [neg_neg, Real.exp_log hp] at hk
  rw [le_div_iff₀ hL]
  linarith

end OptimalOTS
