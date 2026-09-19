import Submissions.Lower.Index
import Mathlib

/-! Exact signing probabilities when the selected message has no cached nonce queries. -/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal
open scoped Classical
noncomputable section

namespace OptimalOTS
namespace FreshSign

variable {P : Params}

def reward (G : Finset ℕ) : Option (Nonce P × Fin P.numSets) → ℝ≥0∞
  | none => 0
  | some p => if p.2.val ∈ G then 1 else 0

/-- For `0 < numSets ≤ 2^idxBits`, the probability of returning a fixed valid index
within `k` independent uniform index trials, stopping at the first valid index. -/
def rate (P : Params) (k : ℕ) : ℝ :=
  (1 - (1 - (P.numSets : ℝ) / 2 ^ P.idxBits) ^ k) / P.numSets

lemma rate_nonneg (hM : P.numSets ≤ 2 ^ P.idxBits) (k : ℕ) : 0 ≤ rate P k := by
  have hN : (0 : ℝ) < 2 ^ P.idxBits := by positivity
  have hMN : (P.numSets : ℝ) ≤ 2 ^ P.idxBits := by exact_mod_cast hM
  have hq : 0 ≤ 1 - (P.numSets : ℝ) / 2 ^ P.idxBits := by
    rw [sub_nonneg, div_le_one hN]; exact hMN
  have hq1 : 1 - (P.numSets : ℝ) / 2 ^ P.idxBits ≤ 1 := sub_le_self _ (by positivity)
  unfold rate
  exact div_nonneg (sub_nonneg.mpr (pow_le_one₀ hq hq1)) (Nat.cast_nonneg _)

lemma rate_succ (hM0 : 0 < P.numSets) (hM : P.numSets ≤ 2 ^ P.idxBits) (k : ℕ) :
    ((2 ^ P.idxBits : ℕ) : ℝ≥0∞) * ENNReal.ofReal (rate P (k + 1)) =
      1 + ((2 ^ P.idxBits - P.numSets : ℕ) : ℝ≥0∞) * ENNReal.ofReal (rate P k) := by
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_natCast (2 ^ P.idxBits - P.numSets),
    ← ENNReal.ofReal_mul (Nat.cast_nonneg _), ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
    ← ENNReal.ofReal_one,
    ← ENNReal.ofReal_add zero_le_one (mul_nonneg (Nat.cast_nonneg _) (rate_nonneg hM k))]
  congr 1
  have hM0' : (0 : ℝ) < P.numSets := by exact_mod_cast hM0
  have hN : (0 : ℝ) < 2 ^ P.idxBits := by positivity
  rw [Nat.cast_sub hM]
  unfold rate
  push_cast
  generalize (2 : ℝ) ^ P.idxBits = N at hN ⊢
  generalize (P.numSets : ℝ) = M at hM0' ⊢
  have hN' : N ≠ 0 := hN.ne'
  have hM' : M ≠ 0 := hM0'.ne'
  have hq : N * (1 - M / N) = N - M := by field_simp
  rw [pow_succ]
  field_simp
  linear_combination (1 - M / N) ^ k * hq + M * (1 - M / N) ^ k * mul_inv_cancel₀ hN'

lemma sum_bitVec_toNat {n : ℕ} (F : ℕ → ℝ≥0∞) :
    ∑ b : BitVec n, F b.toNat = ∑ j ∈ Finset.range (2 ^ n), F j := by
  rw [← Fin.sum_univ_eq_sum_range]
  exact Equiv.sum_comp BitVec.equivFin.toEquiv (fun x : Fin (2 ^ n) => F x.val)

lemma sum_range_mul_mod (a N : ℕ) (G : ℕ → ℝ≥0∞) :
    ∑ j ∈ Finset.range (a * N), G (j % N) = a * ∑ r ∈ Finset.range N, G r := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [add_mul, one_mul, Finset.sum_range_add, ih, Nat.cast_add_one, add_mul, one_mul]
    congr 1
    refine Finset.sum_congr rfl fun r hr => ?_
    rw [Nat.mul_add_mod', Nat.mod_eq_of_lt (Finset.mem_range.mp hr)]

lemma sum_idxOf (hidx : P.idxBits ≤ P.hashBits) (G : ℕ → ℝ≥0∞) :
    ∑ y : BitVec P.hashBits, G (idxOf P y) =
      (2 ^ (P.hashBits - P.idxBits) : ℕ) * ∑ r ∈ Finset.range (2 ^ P.idxBits), G r := by
  have hH : 2 ^ P.hashBits = 2 ^ (P.hashBits - P.idxBits) * 2 ^ P.idxBits := by
    rw [← pow_add, Nat.sub_add_cancel hidx]
  simp only [idxOf, BitVec.toNat_setWidth]
  rw [sum_bitVec_toNat (fun j => G (j % 2 ^ P.idxBits)), hH, sum_range_mul_mod]

lemma sum_branch (G : Finset ℕ) (hG : ∀ i ∈ G, i < P.numSets)
    (hM : P.numSets ≤ 2 ^ P.idxBits) (v : ℝ≥0∞) :
    (∑ r ∈ Finset.range (2 ^ P.idxBits),
      if r < P.numSets then (if r ∈ G then 1 else 0) else v) =
      G.card + ((2 ^ P.idxBits - P.numSets : ℕ) : ℝ≥0∞) * v := by
  have hpoint : ∀ r, (if r < P.numSets then (if r ∈ G then (1 : ℝ≥0∞) else 0) else v) =
      (if r ∈ G then 1 else 0) + (if r < P.numSets then 0 else v) := by
    intro r
    by_cases hrG : r ∈ G
    · simp [hrG, hG r hrG]
    · simp [hrG]
  simp_rw [hpoint]
  rw [Finset.sum_add_distrib]
  congr 1
  · rw [← Finset.sum_filter]
    have hfilter : (Finset.range (2 ^ P.idxBits)).filter (· ∈ G) = G := by
      ext r
      simp only [Finset.mem_filter, Finset.mem_range]
      exact ⟨fun h => h.2, fun h => ⟨(hG r h).trans_le hM, h⟩⟩
    simp [hfilter]
  · rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, nsmul_eq_mul]
    congr 1
    have hfilter : (Finset.range (2 ^ P.idxBits)).filter (fun r => ¬ r < P.numSets) =
        Finset.Ico P.numSets (2 ^ P.idxBits) := by
      ext r
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
      omega
    rw [hfilter, Nat.card_Ico]

lemma uniform_branch (G : Finset ℕ) (hG : ∀ i ∈ G, i < P.numSets)
    (hidx : P.idxBits ≤ P.hashBits) (hM0 : 0 < P.numSets)
    (hM : P.numSets ≤ 2 ^ P.idxBits) (k : ℕ) :
    E ($ᵗ BitVec P.hashBits) (fun w =>
      if idxOf P w < P.numSets then (if idxOf P w ∈ G then 1 else 0)
      else G.card * ENNReal.ofReal (rate P k)) =
      G.card * ENNReal.ofReal (rate P (k + 1)) := by
  rw [E_uniform, ← Finset.mul_sum, sum_idxOf hidx (fun r =>
    if r < P.numSets then (if r ∈ G then 1 else 0) else G.card * ENNReal.ofReal (rate P k)),
    sum_branch G hG hM]
  have hH0 : ((2 ^ P.hashBits : ℕ) : ℝ≥0∞) ≠ 0 := by positivity
  have hHt : ((2 ^ P.hashBits : ℕ) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hH : ((2 ^ P.hashBits : ℕ) : ℝ≥0∞) =
      (2 ^ (P.hashBits - P.idxBits) : ℕ) * ((2 ^ P.idxBits : ℕ) : ℝ≥0∞) := by
    norm_cast
    rw [← pow_add, Nat.sub_add_cancel hidx]
  rw [Fintype.card_bitVec, ← ENNReal.mul_right_inj hH0 hHt, ← mul_assoc,
    ENNReal.mul_inv_cancel hH0 hHt, one_mul]
  rw [hH]
  have hs := rate_succ hM0 hM k
  calc _ = ((2 ^ (P.hashBits - P.idxBits) : ℕ) : ℝ≥0∞) *
      (G.card * (1 + ((2 ^ P.idxBits - P.numSets : ℕ) : ℝ≥0∞) * ENNReal.ofReal (rate P k))) := by ring
    _ = _ := by rw [← hs]; ring

theorem loop_reward (G : Finset ℕ) (hG : ∀ i ∈ G, i < P.numSets)
    (hidx : P.idxBits ≤ P.hashBits) (hM0 : 0 < P.numSets)
    (hM : P.numSets ≤ 2 ^ P.idxBits) (m : Message P) :
    ∀ (k : ℕ) (tried : Finset (Nonce P)) (c : Cache P),
      tried.card + k ≤ 2 ^ P.nonceBits →
      (∀ η ∉ tried, c (encQuery P (m ++ η)) = none) →
      E (run P (signIdxLoop P m k tried) c) (fun p => reward G p.1) =
        G.card * ENNReal.ofReal (rate P k) := by
  intro k
  induction k with
  | zero =>
    intro tried c _ _
    simp [signIdxLoop, run_pure, reward, rate]
  | succ k ih =>
    intro tried c hbudget hfresh
    have hc : 0 < (Finset.univ \ tried).card := by
      rw [Finset.card_univ_sdiff, Fintype.card_bitVec]
      omega
    rw [signIdxLoop_succ P m k tried hc, run_query_bind, oracleImpl_run_inl]
    simp only [bind_assoc, pure_bind, E_bind]
    have hbody : ∀ j, E (run P (loopBody P m k tried (nonceOf P tried hc j)) c)
        (fun p => reward G p.1) = G.card * ENNReal.ofReal (rate P (k + 1)) := by
      intro j
      let η := nonceOf P tried hc j
      have hη : η ∉ tried := (Finset.mem_sdiff.mp (nonceOf_mem P tried hc j)).2
      rw [loopBody, run_query_bind, oracleImpl_run_inr_none P (hfresh η hη)]
      simp only [bind_assoc, pure_bind, E_bind]
      have hkont : ∀ w : BitVec P.hashBits,
          E (run P (afterHash P m k tried η w)
            (c.cacheQuery (encQuery P (m ++ η)) w)) (fun p => reward G p.1) =
          if idxOf P w < P.numSets then (if idxOf P w ∈ G then 1 else 0)
          else G.card * ENNReal.ofReal (rate P k) := by
        intro w
        unfold afterHash
        by_cases hw : idxOf P w < P.numSets
        · rw [dif_pos hw, if_pos hw, run_pure, E_pure]
          rfl
        · rw [dif_neg hw, if_neg hw]
          apply ih
          · rw [Finset.card_insert_of_notMem hη]
            omega
          · intro η' hη'
            have hne : encQuery P (m ++ η') ≠ encQuery P (m ++ η) := by
              intro heq
              have he := append_nonce_inj P m (encQuery_inj P heq)
              exact hη' (he ▸ Finset.mem_insert_self η tried)
            rw [QueryCache.cacheQuery_of_ne _ _ hne]
            exact hfresh η' (fun h => hη' (Finset.mem_insert_of_mem h))
      calc _ = E ($ᵗ BitVec P.hashBits) (fun w =>
          if idxOf P w < P.numSets then (if idxOf P w ∈ G then 1 else 0)
          else G.card * ENNReal.ofReal (rate P k)) := by
            congr 1
            funext w
            exact hkont w
        _ = _ := uniform_branch G hG hidx hM0 hM k
    simp_rw [hbody]
    exact expectedValue_const (by simp) _

/-- A rational upper bound on a repeated-failure probability; no transcendental estimates. -/
lemma one_sub_pow_le_reciprocal {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) (k : ℕ) :
    (1 - p) ^ k ≤ 1 / (1 + (k : ℝ) * p) := by
  have hr : 0 ≤ 1 - p := sub_nonneg.mpr hp1
  have hprod : ∀ n : ℕ, (1 + (n : ℝ) * p) * (1 - p) ^ n ≤ 1 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Nat.cast_add_one, pow_succ]
      have hc : (1 + ((n : ℝ) + 1) * p) * (1 - p) ≤ 1 + (n : ℝ) * p := by
        have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
        nlinarith [sq_nonneg p]
      have hh := mul_le_mul_of_nonneg_right hc (pow_nonneg hr n)
      nlinarith
  have hd : 0 < 1 + (k : ℝ) * p := by positivity
  rw [le_div_iff₀ hd]
  simpa only [mul_comm] using hprod k

/-- The signer selects a good index with probability at least one half, if at least three
quarters of the indices are good and every nonce query for the message starts fresh. -/
theorem paper_reward_ge_half (G : Finset ℕ)
    (hG : ∀ i ∈ G, i < paperParams.numSets)
    (hGcard : 3 * paperParams.numSets ≤ 4 * G.card)
    (m : Message paperParams) (c : Cache paperParams)
    (hfresh : ∀ η : Nonce paperParams, c (encQuery paperParams (m ++ η)) = none) :
    (1 / 2 : ℝ≥0∞) ≤
      E (run paperParams (signIdx paperParams m) c) (fun p => reward G p.1) := by
  rw [signIdx, loop_reward G hG (by decide) (by norm_num [paperParams])
    (by norm_num [paperParams]) m _ ∅ c (by norm_num [paperParams]) (by simpa using hfresh)]
  have hfail := one_sub_pow_le_reciprocal (p := (1 : ℝ) / 8192)
    (by norm_num) (by norm_num) (2 ^ 20)
  norm_num only [Nat.cast_pow, Nat.cast_ofNat] at hfail
  have hrate : (128 : ℝ) / (129 * (2 : ℝ) ^ 115) ≤ rate paperParams paperParams.trialLimit := by
    unfold rate
    change _ ≤ (1 - (1 - ((2 ^ 115 : ℕ) : ℝ) / 2 ^ 128) ^ (2 ^ 20)) /
      ((2 ^ 115 : ℕ) : ℝ)
    norm_num only [Nat.cast_pow, Nat.cast_ofNat]
    rw [le_div_iff₀ (by norm_num)]
    norm_num only
    calc (128 : ℝ) / 129 = 1 - 1 / 129 := by norm_num
      _ ≤ _ := sub_le_sub_left hfail 1
  have hcard : (3 : ℝ) * 2 ^ 115 ≤ 4 * (G.card : ℝ) := by
    exact_mod_cast hGcard
  have hmul := mul_le_mul_of_nonneg_left hrate (Nat.cast_nonneg G.card)
  have hlower : (1 / 2 : ℝ) ≤ (G.card : ℝ) * rate paperParams paperParams.trialLimit := by
    have hn : (0 : ℝ) < 2 ^ 115 := by positivity
    have hgc : (3 * (2 : ℝ) ^ 115) / 4 ≤ G.card := by linarith
    have hnum := mul_le_mul_of_nonneg_right hgc
      (show (0 : ℝ) ≤ 128 / (129 * (2 : ℝ) ^ 115) by positivity)
    norm_num only at hnum
    nlinarith
  have he := ENNReal.ofReal_le_ofReal hlower
  rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast] at he
  norm_num only [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2),
    ENNReal.ofReal_one, ENNReal.ofReal_ofNat] at he
  exact he

end FreshSign
end OptimalOTS
