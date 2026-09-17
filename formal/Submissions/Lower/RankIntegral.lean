import Submissions.Lower.NumericsDefs
import Mathlib

/-!
# From a tail bound to an average

If a nonnegative quantity is below `d` with probability at least
`511/512 - ℓ/500 · (113/d)^21` for every `d ∈ (0, 113]`, then the average of
`max 0 (1 - D/113)` is at least `rankSuccess (ℓ + 1)`.
-/

namespace OptimalOTS

namespace Analysis

open MeasureTheory

lemma integral_indicator_Ioi_le (D c : ℝ) (hc : c ≤ 113) :
    ∫ d in c..113, (Set.Ioi D).indicator (fun _ => (1 : ℝ)) d ≤ max (113 - D) 0 := by
  rw [intervalIntegral.integral_of_le hc, MeasureTheory.integral_indicator measurableSet_Ioi,
    Measure.restrict_restrict measurableSet_Ioi, setIntegral_const, smul_eq_mul, mul_one]
  calc volume.real (Set.Ioi D ∩ Set.Ioc c 113) ≤ volume.real (Set.Ioc D 113) :=
        measureReal_mono (fun x hx => ⟨hx.1, hx.2.2⟩) (by simp)
    _ = max (113 - D) 0 := Real.volume_real_Ioc

lemma intervalIntegrable_indicator_Ioi (D a b : ℝ) :
    IntervalIntegrable (fun d => (Set.Ioi D).indicator (fun _ => (1 : ℝ)) d) volume a b := by
  apply Monotone.intervalIntegrable
  intro x y hxy
  simp only [Set.indicator_apply, Set.mem_Ioi]
  split_ifs with h1 h2 h2
  all_goals first | exact absurd (lt_of_lt_of_le h1 hxy) h2 | norm_num

theorem rankSuccess_le_avg_of_tail {ι : Type*} [Fintype ι] [Nonempty ι] (Dv : ι → ℝ)
    (hD : ∀ k, 0 ≤ Dv k) (ℓ : ℕ) (hℓ₁ : 1 ≤ ℓ) (hℓ : ℓ < 450)
    (htail : ∀ d : ℝ, 0 < d → d ≤ 113 →
      511 / 512 - (ℓ : ℝ) / 500 * (113 / d) ^ 21 ≤
        ((Finset.univ.filter fun k => Dv k < d).card : ℝ) / Fintype.card ι) :
    Numerics.rankSuccess (ℓ + 1) ≤ (∑ k, max 0 (1 - Dv k / 113)) / Fintype.card ι := by
  classical
  set n : ℝ := (Fintype.card ι : ℝ) with hn_def
  have hn : 0 < n := Nat.cast_pos.mpr Fintype.card_pos
  have hℓ0 : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ₁
  have hℓ449 : (ℓ : ℝ) ≤ 449 := by exact_mod_cast (by omega : ℓ ≤ 449)
  set z : ℝ := 512 * (ℓ : ℝ) / 255500 with hz
  have hz0 : 0 < z := by rw [hz]; positivity
  have hz1 : z < 1 := by rw [hz, div_lt_one (by norm_num)]; linarith
  set w : ℝ := z ^ ((1 : ℝ) / 21) with hw
  have hw0 : 0 < w := Real.rpow_pos_of_pos hz0 _
  have hw1 : w ≤ 1 := Real.rpow_le_one hz0.le hz1.le (by norm_num)
  have hwz : w ^ 21 = z := by
    rw [hw, ← Real.rpow_natCast, ← Real.rpow_mul hz0.le]; norm_num
  have hR : Numerics.rankSuccess (ℓ + 1) = 511 / 512 * (1 - 21 / 20 * w + z / 20) := by
    rw [Numerics.rankSuccess, if_neg (by omega)]
    simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
    rfl
  have hℓw : (ℓ : ℝ) = 255500 * w ^ 21 / 512 := by rw [hwz, hz]; ring
  set c : ℝ := 113 * w with hc_def
  have hc0 : 0 < c := by positivity
  have hc : c ≤ 113 := by rw [hc_def]; nlinarith
  set G : ℝ → ℝ := fun d => ∑ k, (Set.Ioi (Dv k)).indicator (fun _ => (1 : ℝ)) d with hG
  have hcard : ∀ d, ((Finset.univ.filter fun k => Dv k < d).card : ℝ) = G d := by
    intro d
    rw [Finset.natCast_card_filter]
    simp [G, Set.indicator_apply]
  -- the lower integrand and its antiderivative
  set f : ℝ → ℝ := fun d => n * (511 / 512 - (ℓ : ℝ) / 500 * (113 / d) ^ 21) with hf
  set F : ℝ → ℝ := fun d => n * (511 / 512 * d + (ℓ : ℝ) / 500 * 113 ^ 21 / 20 * (d ^ 20)⁻¹)
    with hF
  have hderiv : ∀ x ∈ Set.uIcc c 113, HasDerivAt F (f x) x := by
    intro x hx
    rw [Set.uIcc_of_le hc] at hx
    have hx0 : x ≠ 0 := (hc0.trans_le hx.1).ne'
    have h1 := (((hasDerivAt_id x).const_mul (511 / 512 : ℝ)).add
      (((hasDerivAt_pow 20 x).inv (pow_ne_zero 20 hx0)).const_mul
        ((ℓ : ℝ) / 500 * 113 ^ 21 / 20))).const_mul n
    have h2 : HasDerivAt F (n * (511 / 512 * 1 + (ℓ : ℝ) / 500 * 113 ^ 21 / 20 *
        (-((20 : ℕ) * x ^ (20 - 1)) / (x ^ 20) ^ 2))) x := h1
    refine h2.congr_deriv ?_
    show n * (511 / 512 * 1 + (ℓ : ℝ) / 500 * 113 ^ 21 / 20 *
        (-((20 : ℕ) * x ^ (20 - 1)) / (x ^ 20) ^ 2)) = n * (511 / 512 - (ℓ : ℝ) / 500 * (113 / x) ^ 21)
    congr 1
    norm_num
    field_simp
    ring
  have hfint : IntervalIntegrable f volume c 113 := by
    apply ContinuousOn.intervalIntegrable
    intro x hx
    rw [Set.uIcc_of_le hc] at hx
    have hx0 : x ≠ 0 := (hc0.trans_le hx.1).ne'
    apply ContinuousAt.continuousWithinAt
    show ContinuousAt (fun d : ℝ => n * (511 / 512 - (ℓ : ℝ) / 500 * (113 / d) ^ 21)) x
    fun_prop (disch := exact hx0)
  have hint : ∫ d in c..113, f d = n * (113 * (511 / 512 * (1 - 21 / 20 * w + z / 20))) := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hfint]
    simp only [hF, hc_def]
    rw [← hwz, hℓw]
    field_simp
    ring
  have hmono : ∫ d in c..113, f d ≤ ∫ d in c..113, G d := by
    apply intervalIntegral.integral_mono_on hc hfint
    · have := IntervalIntegrable.sum Finset.univ
        (fun k _ => intervalIntegrable_indicator_Ioi (Dv k) c 113)
      rwa [Finset.sum_fn] at this
    · intro d hd
      have h := htail d (hc0.trans_le hd.1) hd.2
      rw [hcard, le_div_iff₀ hn] at h
      simp only [hf]
      linarith
  have hsum : ∫ d in c..113, G d ≤ 113 * ∑ k, max 0 (1 - Dv k / 113) := by
    simp only [hG]
    rw [intervalIntegral.integral_finsetSum
      (fun k _ => intervalIntegrable_indicator_Ioi (Dv k) c 113), Finset.mul_sum]
    gcongr with k
    refine (integral_indicator_Ioi_le (Dv k) c hc).trans (le_of_eq ?_)
    rw [mul_max_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 113), max_comm]
    congr 1 <;> ring
  rw [hR, le_div_iff₀ hn]
  nlinarith

end Analysis

end OptimalOTS
