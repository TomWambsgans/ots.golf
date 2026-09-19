import Submissions.RiscvUpper.Assembly
import Submissions.RiscvUpper.Scheme
import Submissions.RiscvUpper.Adapter

/-!
# Signing availability of the forest algorithm

Key generation makes no 512-bit index query. For any message chosen from the public key,
the signer therefore tries fresh, distinct nonce queries. Each trial fails with probability
`miss = 1 - numValid / 2 ^ 128 ≤ 8191 / 8192`, and the `2^20` trials give failure at most
`2^-128`.
-/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal
noncomputable section
open scoped Classical

namespace OptimalOTS.Forest.Availability

attribute [local irreducible] Finset.univ Finset.filter validSet numValid

/-- Failure probability of one fresh index query. -/
def miss : ℝ≥0∞ :=
  ((2 ^ 256 - numValid paperParams * 2 ^ 128 : ℕ) : ℝ≥0∞) * (((2 ^ 256 : ℕ) : ℝ≥0∞))⁻¹

theorem miss_eq : miss = ((2 ^ 256 - numValid paperParams * 2 ^ 128 : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
  rw [miss, div_eq_mul_inv, Nat.cast_pow, Nat.cast_ofNat]

/-- At least `2 ^ 115` of the `2 ^ 128` indices are accepted. -/
theorem miss_le : miss ≤ 8191 / 8192 := by
  have hN : 2 ^ 243 ≤ numValid paperParams * 2 ^ 128 :=
    calc 2 ^ 243 = 2 ^ 115 * 2 ^ 128 := by norm_num
      _ ≤ _ := Nat.mul_le_mul_right _ numValid_ge
  have ha : 2 ^ 256 - numValid paperParams * 2 ^ 128 ≤ 8191 * 2 ^ 243 := by
    have h := Nat.sub_le_sub_left hN (2 ^ 256)
    have e : 2 ^ 256 - 2 ^ 243 = 8191 * 2 ^ 243 := by norm_num
    omega
  calc miss = ((2 ^ 256 - numValid paperParams * 2 ^ 128 : ℕ) : ℝ≥0∞) / 2 ^ 256 := miss_eq
    _ ≤ ((8191 * 2 ^ 243 : ℕ) : ℝ≥0∞) / 2 ^ 256 := ENNReal.div_le_div_right (Nat.cast_le.mpr ha) _
    _ = 8191 / 8192 := by
      rw [ENNReal.div_eq_div_iff (by norm_num) (by finiteness) (by norm_num) (by finiteness)]
      norm_num

private theorem uniform_miss_count (P : Params) (hidx : P.idxBits ≤ P.hashBits)
    (hM : numValid P ≤ 2 ^ P.idxBits) (a : ℝ≥0∞) :
    E ($ᵗ BitVec P.hashBits) (fun w => if idxOf P w ∈ validSet P then 0 else a) =
      ((2 ^ P.hashBits - numValid P * 2 ^ (P.hashBits - P.idxBits) : ℕ) : ℝ≥0∞) *
        (((2 ^ P.hashBits : ℕ) : ℝ≥0∞)⁻¹ * a) := by
  have hv : (Finset.univ.filter fun w : BitVec P.hashBits => idxOf P w ∈ validSet P).card =
      numValid P * 2 ^ (P.hashBits - P.idxBits) := by
    have h := Analysis.card_idxOfOut_mem (P := P) hidx (validSet P)
      (fun n hn => mem_validSet_lt hn)
    convert h using 1 <;> simp [Analysis.idxOfOut, idxOf, numValid]
  have hn : (Finset.univ.filter fun w : BitVec P.hashBits => ¬ idxOf P w ∈ validSet P).card =
      2 ^ P.hashBits - numValid P * 2 ^ (P.hashBits - P.idxBits) := by
    have h := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (BitVec P.hashBits)))
      (p := fun w => idxOf P w ∈ validSet P)
    rw [hv, Finset.card_univ, Fintype.card_bitVec] at h
    omega
  rw [E_uniform]
  simp only [mul_ite, mul_zero]
  rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const,
    nsmul_eq_mul, hn, Fintype.card_bitVec]

private theorem uniform_miss (a : ℝ≥0∞) :
    E ($ᵗ BitVec paperParams.hashBits)
      (fun w => if idxOf paperParams w ∈ validSet paperParams then 0 else a) = miss * a := by
  rw [uniform_miss_count paperParams (by decide) (numValid_le paperParams), ← mul_assoc]
  have h1 : paperParams.hashBits = 256 := rfl
  have h2 : paperParams.hashBits - paperParams.idxBits = 128 := rfl
  rw [h2, h1]
  rfl

/-- Exact failure probability while enough untried nonces remain and their queries are fresh. -/
theorem loop_failure (m : Message paperParams) :
    ∀ (k : ℕ) (tried : Finset (Nonce paperParams)) (c : Cache paperParams),
      tried.card + k ≤ 2 ^ paperParams.nonceBits →
      (∀ η ∉ tried, c (encQuery paperParams (m ++ η)) = none) →
      E (run paperParams (signIdxLoop paperParams m k tried) c)
        (fun p => if p.1.isNone then 1 else 0) = miss ^ k := by
  intro k
  induction k with
  | zero =>
    intro tried c _ _
    simp [signIdxLoop, run_pure]
  | succ k ih =>
    intro tried c hbudget hfresh
    have hc : 0 < (Finset.univ \ tried).card := by
      rw [Finset.card_univ_sdiff, Fintype.card_bitVec]
      omega
    rw [signIdxLoop_succ paperParams m k tried hc, run_query_bind, oracleImpl_run_inl]
    simp only [bind_assoc, pure_bind, E_bind]
    have hbody : ∀ j,
        E (run paperParams (loopBody paperParams m k tried (nonceOf paperParams tried hc j)) c)
          (fun p => if p.1.isNone then 1 else 0) = miss ^ (k + 1) := by
      intro j
      let η := nonceOf paperParams tried hc j
      have hη : η ∉ tried := (Finset.mem_sdiff.mp (nonceOf_mem paperParams tried hc j)).2
      rw [loopBody, run_query_bind, oracleImpl_run_inr_none paperParams (hfresh η hη)]
      simp only [bind_assoc, pure_bind, E_bind]
      have hkont : ∀ w : BitVec paperParams.hashBits,
          E (run paperParams (afterHash paperParams m k tried η w)
            (c.cacheQuery (encQuery paperParams (m ++ η)) w))
            (fun p => if p.1.isNone then 1 else 0) =
          if idxOf paperParams w ∈ validSet paperParams then 0 else miss ^ k := by
        intro w
        unfold afterHash
        by_cases hw : idxOf paperParams w ∈ validSet paperParams
        · rw [dif_pos hw, if_pos hw, run_pure, E_pure]
          rfl
        · rw [dif_neg hw, if_neg hw]
          apply ih
          · rw [Finset.card_insert_of_notMem hη]
            omega
          · intro η' hη'
            have hne : encQuery paperParams (m ++ η') ≠ encQuery paperParams (m ++ η) := by
              intro heq
              have he := append_nonce_inj paperParams m (encQuery_inj paperParams heq)
              exact hη' (he ▸ Finset.mem_insert_self η tried)
            rw [QueryCache.cacheQuery_of_ne _ _ hne]
            exact hfresh η' (fun h => hη' (Finset.mem_insert_of_mem h))
      calc
        _ = E ($ᵗ BitVec paperParams.hashBits)
            (fun w => if idxOf paperParams w ∈ validSet paperParams then 0 else miss ^ k) := by
          congr 1
          funext w
          exact hkont w
        _ = _ := by rw [uniform_miss, pow_succ, mul_comm]
    simp_rw [hbody]
    exact expectedValue_const (by simp) _

/-- A rational bound on repeated failure; it avoids real exponentials. -/
private theorem bernoulli_reciprocal {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) (k : ℕ) :
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

/-- A block of 8192 trials fails with probability at most one half. -/
private theorem miss_block : miss ^ 8192 ≤ 1 / 2 := by
  refine (pow_le_pow_left' miss_le 8192).trans ?_
  have h := bernoulli_reciprocal (p := (1 : ℝ) / 8192) (by norm_num) (by norm_num) 8192
  have hbase : (1 : ℝ) - 1 / 8192 = 8191 / 8192 := by norm_num
  have hden : 1 + ((8192 : ℕ) : ℝ) * (1 / 8192) = 2 := by norm_num
  rw [hbase, hden] at h
  have h' := ENNReal.ofReal_le_ofReal h
  rw [ENNReal.ofReal_pow (by norm_num)] at h'
  have hb : ENNReal.ofReal ((8191 : ℝ) / 8192) = (8191 / 8192 : ℝ≥0∞) := by
    norm_num [ENNReal.ofReal_div_of_pos]
  have hh : ENNReal.ofReal ((1 : ℝ) / 2) = (1 / 2 : ℝ≥0∞) := by
    norm_num [ENNReal.ofReal_div_of_pos]
  rwa [hb, hh] at h'

/-- The full signing budget contains 128 blocks, each with failure at most one half. -/
theorem miss_trials_le : miss ^ paperParams.trialLimit ≤ 1 / 2 ^ 128 := by
  change miss ^ (8192 * 128) ≤ 1 / 2 ^ 128
  rw [pow_mul]
  calc
    (miss ^ 8192) ^ 128 ≤ (1 / 2 : ℝ≥0∞) ^ 128 := pow_le_pow_left' miss_block _
    _ = 1 / 2 ^ 128 := by simp only [one_div, ENNReal.inv_pow]

/-- Signing has the same failure probability for every message and every fresh index cache. -/
theorem sign_failure (x : forestScheme.graph.Assignment) (m : Message paperParams)
    (c : Cache paperParams) (hfresh : ∀ η : Nonce paperParams, c (encQuery paperParams (m ++ η)) = none) :
    E (run paperParams (forestScheme.sign x m) c)
      (fun p => if p.1.isNone then 1 else 0) = miss ^ paperParams.trialLimit := by
  rw [sign_eq_map, run_map, E_map]
  simp only [Option.isNone_map]
  exact loop_failure m _ ∅ c (by norm_num [paperParams]) (fun η _ => hfresh η)

/-- Failure remains bounded even when the message is chosen after seeing the public key. -/
theorem signingFailure_strong :
    forestScheme.toAlgorithm.SigningFailureAtMost (1 / 2 ^ 128 : ℝ≥0∞) := by
  intro message
  change probTrue paperParams (do
    let kg ← forestScheme.keygen
    let σ ← forestScheme.sign kg.2 (message kg.1)
    pure σ.isNone) ≤ _
  rw [probTrue_eq_E_run, run_bind, E_bind, E_run_keygen_forest]
  simp only [run_bind, E_bind, run_pure, E_pure]
  have hs : ∀ ξ : Rec,
      E (run paperParams (forestScheme.sign (graph.evalRec ξ) (message (pkOf ξ))) (kc ξ))
        (fun p => if p.1.isNone then 1 else 0) = miss ^ paperParams.trialLimit := by
    intro ξ
    exact sign_failure _ _ _ (fun η => kc_enc ξ _)
  simp_rw [hs]
  rw [← Finset.sum_mul, sum_w, one_mul]
  exact miss_trials_le

end OptimalOTS.Forest.Availability

namespace OptimalOTS.GenericAvailability

/-- The forest algorithm meets the generic upper challenge's signing-failure allowance. -/
theorem signingFailure :
    Forest.forestScheme.toAlgorithm.SigningFailureAtMost (1 / 2 ^ 128 : ℝ≥0∞) := by
  intro message
  exact (Forest.Availability.signingFailure_strong message).trans (by norm_num)

end OptimalOTS.GenericAvailability
