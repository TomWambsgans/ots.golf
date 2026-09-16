import OptimalOTS.Proof.NumericsDefs

/-!
# The numerical success-probability bound

Certificate from Appendix B of the paper: `omega ℓ ≥ (3/128) (c^ℓ - 2^-110)` with `c ≤ exp(-3/128)`
rational, `rankSuccess ℓ ≥ bb ℓ` via tabulated rational upper bounds on `z_ℓ^(1/22)`, and
`signFailure ≤ exp(-256) ≤ 1/257`. The resulting rational sum is checked by kernel evaluation.
-/

namespace OptimalOTS.Numerics

namespace SuccessAux

/-- `rTab[ℓ - 2] / 2^20` is an upper bound on `(512 (ℓ - 1) / 51100)^(1/22)`. -/
def rTab : List ℕ := [850608, 877835, 894164, 905933, 915168, 922784, 929273, 934930, 939949, 944461, 948562, 952321, 955792, 959017, 962029, 964856, 967518, 970035, 972422, 974692, 976856, 978924, 980904, 982803, 984628, 986385, 988079, 989714, 991294, 992822, 994303, 995739, 997133, 998487, 999803, 1001084, 1002332, 1003548, 1004733, 1005890, 1007020, 1008123, 1009202, 1010257, 1011290, 1012301, 1013291, 1014261, 1015212, 1016145, 1017060, 1017958, 1018840, 1019706, 1020556, 1021393, 1022215, 1023023, 1023818, 1024601, 1025371, 1026129, 1026876, 1027611, 1028335, 1029049, 1029753, 1030447, 1031131, 1031805, 1032471, 1033127, 1033775, 1034415, 1035046, 1035669, 1036285, 1036893, 1037494, 1038087, 1038673, 1039253, 1039825, 1040392, 1040951, 1041505, 1042052, 1042594, 1043130, 1043659, 1044184, 1044703, 1045216, 1045724, 1046228, 1046726, 1047219, 1047707, 1048191]

/-- A rational lower bound on `exp (-3/128)`. -/
def cc : ℚ := 8390948729 / 8589934592

/-- Rational lower bound on `rankSuccess ℓ`. -/
def bb (ℓ : ℕ) : ℚ :=
  if ℓ = 1 then 1 else
    511 / 512 * (1 - 22 / 21 * ((rTab.getD (ℓ - 2) 0 : ℚ) / 2 ^ 20) +
      (512 * ((ℓ : ℚ) - 1) / 51100) / 21)

/-- Rational lower bound on `omega ℓ * rankSuccess ℓ`. -/
def gg (ℓ : ℕ) : ℚ := 3 / 128 * (cc ^ ℓ - 1 / 2 ^ 110) * bb ℓ

theorem tab_ok : ∀ ℓ < 101, 2 ≤ ℓ →
    512 * (ℓ - 1) * (2 ^ 20) ^ 22 ≤ 51100 * (rTab.getD (ℓ - 2) 0) ^ 22 := by
  decide +kernel

theorem nonneg_ok : ∀ ℓ < 101, 1 ≤ ℓ → 0 ≤ bb ℓ ∧ 1 / 2 ^ 110 ≤ cc ^ ℓ := by
  decide +kernel

theorem sum_ok : (11 / 200 : ℚ) < 256 / 257 * ∑ ℓ ∈ Finset.Icc 1 100, gg ℓ := by
  decide +kernel


theorem cc_le_exp : ((cc : ℚ) : ℝ) ≤ Real.exp (-(3 / 128)) := by
  have h := Real.exp_bound (x := -(3 / 128 : ℝ)) (by norm_num [abs_of_neg]) (n := 4) (by norm_num)
  have h' := (abs_le.1 h).1
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h'
  norm_num [abs_of_neg] at h'
  simp only [cc]
  push_cast
  linarith

theorem omega_ge (ℓ : ℕ) (h1 : 1 ≤ ℓ) (h100 : ℓ ≤ 100) :
    3 / 128 * (((cc : ℚ) : ℝ) ^ ℓ - 1 / 2 ^ 110) ≤ omega ℓ := by
  have hN : (N : ℝ) = 2 ^ 128 := by norm_num [N]
  have hTN : (T : ℝ) * (1 / N) = 3 / 128 := by rw [hN]; norm_num [T]
  have hx1 : (1 : ℝ) ≤ ℓ := by exact_mod_cast h1
  have hx100 : (ℓ : ℝ) ≤ 100 := by exact_mod_cast h100
  set x : ℝ := (ℓ : ℝ) with hx
  set b : ℝ := 1 - x / N with hb
  have hxN : x / N ≤ 1 / 2 ^ 120 := by
    rw [hN, div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
  have hxN0 : 0 ≤ x / N := by rw [hN]; positivity
  have hbpos : 0 < b := by rw [hb]; linarith [show (1 : ℝ) / 2 ^ 120 < 1 / 2 by norm_num]
  have hb2 : 1 / 2 ≤ b := by rw [hb]; linarith [show (1 : ℝ) / 2 ^ 120 < 1 / 2 by norm_num]
  have hb1 : b ≤ 1 := by rw [hb]; linarith
  have hNpos : (0 : ℝ) < N := by rw [hN]; positivity
  -- Step A: omega ℓ ≥ (T / N) b ^ T
  have hA : 3 / 128 * b ^ T ≤ omega ℓ := by
    have hd : 1 - (x - 1) / N = b * (1 + 1 / N / b) := by
      rw [mul_add, mul_one, mul_div_cancel₀ _ hbpos.ne', hb]; ring
    unfold omega
    rw [← hx, hd, mul_pow]
    have hbern := one_add_mul_le_pow (a := 1 / N / b)
      (by have : 0 ≤ 1 / N / b := by positivity
          linarith) T
    have hdb : (1 : ℝ) / N ≤ 1 / N / b := le_div_self (by positivity) hbpos hb1
    have hbT : 0 < b ^ T := pow_pos hbpos T
    have hT0 : (0 : ℝ) ≤ T := Nat.cast_nonneg T
    calc 3 / 128 * b ^ T = b ^ T * (T * (1 / N)) := by rw [hTN]; ring
      _ ≤ b ^ T * (T * (1 / N / b)) := by gcongr
      _ = b ^ T * (1 + T * (1 / N / b)) - b ^ T := by ring
      _ ≤ b ^ T * (1 + 1 / N / b) ^ T - b ^ T := by gcongr
  -- Step B: b ^ T ≥ exp (-(x * 3 / 128)) - 2^-110
  have hkey : -(x * (3 / 128)) - 1 / 2 ^ 110 ≤ (T : ℝ) * (1 - b⁻¹) := by
    have he : (T : ℝ) * (1 - b⁻¹) = -(3 / 128 * x / b) := by
      rw [← hTN]; field_simp; rw [hb]; field_simp; ring
    have h5 : x * (x / N) ≤ 100 * (1 / 2 ^ 120) := mul_le_mul hx100 hxN hxN0 (by norm_num)
    have h6 : (x * (3 / 128) + 1 / 2 ^ 110) * b =
        x * (3 / 128) - 3 / 128 * (x * (x / N)) + 1 / 2 ^ 110 * b := by rw [hb]; ring
    have h7 : 3 / 128 * x / b ≤ x * (3 / 128) + 1 / 2 ^ 110 := by
      rw [div_le_iff₀ hbpos, h6]; nlinarith [h5, hb2]
    rw [he]; linarith
  have hB : Real.exp (-(x * (3 / 128))) - 1 / 2 ^ 110 ≤ b ^ T := by
    have hlog : 1 - b⁻¹ ≤ Real.log b := Real.one_sub_inv_le_log_of_pos hbpos
    have hbT : b ^ T = Real.exp (T * Real.log b) := by
      rw [Real.exp_nat_mul, Real.exp_log hbpos]
    have hT0 : (0 : ℝ) ≤ T := Nat.cast_nonneg T
    have h2 : Real.exp (-(x * (3 / 128)) - 1 / 2 ^ 110) ≤ b ^ T := by
      rw [hbT]; apply Real.exp_le_exp.2
      calc _ ≤ (T : ℝ) * (1 - b⁻¹) := hkey
        _ ≤ T * Real.log b := by gcongr
    have hE : Real.exp (-(x * (3 / 128))) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
    have hE0 := Real.exp_pos (-(x * (3 / 128)))
    have h3 : 1 - 1 / 2 ^ 110 ≤ Real.exp (-(1 / 2 ^ 110 : ℝ)) := Real.one_sub_le_exp_neg _
    rw [sub_eq_add_neg, Real.exp_add] at h2
    nlinarith
  have hC : ((cc : ℚ) : ℝ) ^ ℓ ≤ Real.exp (-(x * (3 / 128))) := by
    rw [show -(x * (3 / 128)) = (ℓ : ℝ) * (-(3 / 128)) by rw [hx]; ring, Real.exp_nat_mul]
    apply pow_le_pow_left₀ (by simp only [cc]; norm_num) cc_le_exp
  nlinarith

theorem rank_ge (ℓ : ℕ) (h1 : 1 ≤ ℓ) (h100 : ℓ ≤ 100) : ((bb ℓ : ℚ) : ℝ) ≤ rankSuccess ℓ := by
  unfold bb rankSuccess
  by_cases h : ℓ = 1
  · simp [h]
  · simp only [if_neg h]
    have h2 : 2 ≤ ℓ := by omega
    have ht := tab_ok ℓ (by omega) h2
    have hx1 : (1 : ℝ) ≤ ℓ := by exact_mod_cast h1
    set K := rTab.getD (ℓ - 2) 0
    have hz0 : (0 : ℝ) ≤ 512 * ((ℓ : ℝ) - 1) / 51100 := by
      have : (0 : ℝ) ≤ (ℓ : ℝ) - 1 := by linarith
      positivity
    have hr : 512 * ((ℓ : ℝ) - 1) / 51100 ≤ ((K : ℝ) / 2 ^ 20) ^ 22 := by
      have : ((512 * (ℓ - 1) * (2 ^ 20) ^ 22 : ℕ) : ℝ) ≤ ((51100 * K ^ 22 : ℕ) : ℝ) := by
        exact_mod_cast ht
      push_cast [Nat.cast_sub h1] at this
      rw [div_pow, div_le_div_iff₀ (by norm_num) (by positivity)]
      linarith
    have hroot : (512 * ((ℓ : ℝ) - 1) / 51100) ^ ((1 : ℝ) / 22) ≤ (K : ℝ) / 2 ^ 20 := by
      calc (512 * ((ℓ : ℝ) - 1) / 51100) ^ ((1 : ℝ) / 22)
          ≤ (((K : ℝ) / 2 ^ 20) ^ 22) ^ ((1 : ℝ) / 22) :=
            Real.rpow_le_rpow hz0 hr (by norm_num)
        _ = (K : ℝ) / 2 ^ 20 := by
          rw [show ((1 : ℝ) / 22) = ((22 : ℕ) : ℝ)⁻¹ by norm_num]
          exact Real.pow_rpow_inv_natCast (by positivity) (by norm_num)
    push_cast
    nlinarith

theorem signFailure_le : signFailure ≤ 1 / 257 := by
  unfold signFailure
  have h1 : (0 : ℝ) ≤ 1 - (2 : ℝ)⁻¹ ^ 13 := by norm_num
  calc (1 - (2 : ℝ)⁻¹ ^ 13) ^ (2 ^ 21)
      ≤ (Real.exp (-((2 : ℝ)⁻¹ ^ 13))) ^ (2 ^ 21) :=
        pow_le_pow_left₀ h1 (Real.one_sub_le_exp_neg _) _
    _ = Real.exp (-256) := by
        rw [← Real.exp_nat_mul]; norm_num
    _ ≤ 1 / 257 := by
        rw [Real.exp_neg, ← one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
        linarith [Real.add_one_le_exp 256]

theorem sum_ge : ((∑ ℓ ∈ Finset.Icc 1 100, gg ℓ : ℚ) : ℝ) ≤
    ∑ ℓ ∈ Finset.Icc 1 100, omega ℓ * rankSuccess ℓ := by
  rw [Rat.cast_sum]
  apply Finset.sum_le_sum
  intro ℓ hℓ
  rw [Finset.mem_Icc] at hℓ
  obtain ⟨hb0, hc⟩ := nonneg_ok ℓ (by omega) hℓ.1
  have hω := omega_ge ℓ hℓ.1 hℓ.2
  have hr := rank_ge ℓ hℓ.1 hℓ.2
  have hc' : ((1 / 2 ^ 110 : ℚ) : ℝ) ≤ ((cc ^ ℓ : ℚ) : ℝ) := by exact_mod_cast hc
  push_cast at hc'
  have hA : (0 : ℝ) ≤ 3 / 128 * (((cc : ℚ) : ℝ) ^ ℓ - 1 / 2 ^ 110) := by nlinarith
  have hB : (0 : ℝ) ≤ ((bb ℓ : ℚ) : ℝ) := by exact_mod_cast hb0
  unfold gg
  push_cast
  exact mul_le_mul hω hr hB (hA.trans hω)

end SuccessAux

theorem success_lt :
    11 / 200 < (1 - signFailure) * ∑ ℓ ∈ Finset.Icc 1 100, omega ℓ * rankSuccess ℓ := by
  have hq : (11 / 200 : ℝ) < 256 / 257 * ((∑ ℓ ∈ Finset.Icc 1 100, SuccessAux.gg ℓ : ℚ) : ℝ) := by
    have := (Rat.cast_lt (K := ℝ)).2 SuccessAux.sum_ok
    simpa only [Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat] using this
  have hs := SuccessAux.sum_ge
  have hF := SuccessAux.signFailure_le
  have hG : (0 : ℝ) ≤ ((∑ ℓ ∈ Finset.Icc 1 100, SuccessAux.gg ℓ : ℚ) : ℝ) := by nlinarith
  calc (11 / 200 : ℝ) < 256 / 257 * ((∑ ℓ ∈ Finset.Icc 1 100, SuccessAux.gg ℓ : ℚ) : ℝ) := hq
    _ ≤ (1 - signFailure) * ∑ ℓ ∈ Finset.Icc 1 100, omega ℓ * rankSuccess ℓ :=
        mul_le_mul (by linarith) hs hG (by linarith)

end OptimalOTS.Numerics
