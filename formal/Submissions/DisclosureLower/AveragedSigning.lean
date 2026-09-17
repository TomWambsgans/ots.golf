import Submissions.DisclosureLower.SignFresh
import Submissions.DisclosureLower.CacheFresh

/-! A fresh signing index has the same weight for every index. -/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal
noncomputable section
open scoped Classical

namespace OptimalOTS.AveragedSigning

def reward {P : Params} (f : Fin P.numSets → ℝ≥0∞) :
    Option (Nonce P × Fin P.numSets) → ℝ≥0∞
  | none => 0
  | some p => f p.2

theorem reward_eq_sum {P : Params} (f : Fin P.numSets → ℝ≥0∞)
    (r : Option (Nonce P × Fin P.numSets)) :
    reward f r = ∑ i, FreshSign.reward {i.val} r * f i := by
  cases r with
  | none => simp [reward, FreshSign.reward]
  | some r =>
    rcases r with ⟨η,j⟩
    simp only [reward, FreshSign.reward, Finset.mem_singleton]
    rw [Finset.sum_eq_single j]
    · simp
    · intro i _ hij
      have hne : j.val ≠ i.val := fun h => hij (Fin.ext h.symm)
      simp [hne]
    · simp

theorem E_finset_sum {α ι : Type} (p : ProbComp α) (s : Finset ι)
    (f : ι → α → ℝ≥0∞) :
    E p (fun x => ∑ i ∈ s, f i x) = ∑ i ∈ s, E p (f i) := by
  exact expectedValue_finsetSum p s f

theorem sign_reward_eq (f : Fin paperParams.numSets → ℝ≥0∞)
    (m : Message paperParams) (c : Cache paperParams)
    (hfresh : BareLower.FreshMessage c m) :
    E (run paperParams (signIdx paperParams m) c) (fun p => reward f p.1) =
      ENNReal.ofReal (FreshSign.rate paperParams paperParams.trialLimit) * ∑ i, f i := by
  simp_rw [reward_eq_sum]
  rw [E_finset_sum]
  simp_rw [E, expectedValue_mul_const]
  have hsingle : ∀ i : Fin paperParams.numSets,
      E (run paperParams (signIdx paperParams m) c)
        (fun p => FreshSign.reward {i.val} p.1) =
      ENNReal.ofReal (FreshSign.rate paperParams paperParams.trialLimit) := by
    intro i
    rw [signIdx, FreshSign.loop_reward {i.val} (by simp only [Finset.mem_singleton]; intro n hn; simpa only [hn] using i.isLt)
      (by decide) (by norm_num [paperParams]) (by norm_num [paperParams]) m _ ∅ c
      (by norm_num [paperParams]) (by intro η _; exact hfresh η)]
    simp
  change (∑ i, E (run paperParams (signIdx paperParams m) c)
      (fun p => FreshSign.reward {i.val} p.1) * f i) = _
  simp_rw [hsingle]
  rw [Finset.mul_sum]

theorem paper_rate_ge :
    (256 : ℝ) / (257 * (2 : ℝ) ^ 115) ≤
      FreshSign.rate paperParams paperParams.trialLimit := by
  have hfail := FreshSign.one_sub_pow_le_reciprocal (p := (1 : ℝ) / 8192)
    (by norm_num) (by norm_num) (2 ^ 21)
  norm_num only [Nat.cast_pow, Nat.cast_ofNat] at hfail
  unfold FreshSign.rate
  change _ ≤ (1 - (1 - ((2 ^ 115 : ℕ) : ℝ) / 2 ^ 128) ^ (2 ^ 21)) /
    ((2 ^ 115 : ℕ) : ℝ)
  norm_num only [Nat.cast_pow, Nat.cast_ofNat]
  rw [le_div_iff₀ (by norm_num)]
  norm_num only
  calc (256 : ℝ) / 257 = 1 - 1 / 257 := by norm_num
    _ ≤ _ := sub_le_sub_left hfail 1

end OptimalOTS.AveragedSigning
