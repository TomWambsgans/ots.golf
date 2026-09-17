import Submissions.Lower.AnalysisDefs

/-!
# The index selected by signing

Averaged over a uniform nonce table, signing returns each valid index `i` with probability
`(1 - (1 - M / 2^idxBits) ^ L) / M`, whatever the signer's values.
-/

open OracleSpec OracleComp ENNReal

noncomputable section

open scoped Classical

namespace OptimalOTS

namespace Analysis

variable {P : Params} (S : Scheme P)

lemma setWidth_append_nonce (m : Message P) (η : Nonce P) :
    (m ++ η).setWidth P.nonceBits = η := by
  ext j hj
  simp [BitVec.getElem_setWidth, BitVec.getLsbD_append, hj]

lemma simulateQ_index (u : Nonce P → BitVec P.hashBits) (m : Message P) (η : Nonce P) :
    simulateQ (signImpl P u) (index P m η) = pure (idxOfOut P (u η)) := by
  simp [index, hash, signImpl, idxOfOut, setWidth_append_nonce]

lemma simulateQ_unif (u : Nonce P → BitVec P.hashBits) (n : ℕ) :
    simulateQ (signImpl P u) (liftM ($[0..n]) : OracleComp (Spec P) (Fin (n + 1))) = $[0..n] := by
  simp [signImpl, QueryImpl.simulateQ_add_liftM_left, QueryImpl.simulateQ_toQueryImpl]

lemma sum_fin_equivFin {α : Type*} {s : Finset α} {n : ℕ} (h : n = s.card) (G : α → ℝ≥0∞) :
    ∑ j : Fin n, G (s.equivFin.symm (Fin.cast h j)).1 = ∑ η ∈ s, G η := by
  rw [← Finset.sum_coe_sort s]
  exact Equiv.sum_comp ((finCongr h).trans s.equivFin.symm) (fun x => G x.1)

lemma sum_ite_sum_mul {α β : Type*} [Fintype α] (s : Finset β) (w : ℝ≥0∞) (p : α → Prop)
    [DecidablePred p] (Q : α → β → ℝ≥0∞) :
    (∑ a, if p a then ∑ b ∈ s, w * Q a b else 0) =
      ∑ b ∈ s, w * ∑ a, (if p a then Q a b else 0) := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  split_ifs <;> simp

/-- The probability that the signing loop succeeds with index `i`, as a pure recursion. -/
def loopVal (u : Nonce P → BitVec P.hashBits) (i : Fin P.numSets) :
    ℕ → Finset (Nonce P) → ℝ≥0∞
  | 0, _ => 0
  | k + 1, Tr =>
    (∑ η ∈ Finset.univ \ Tr, if idxOfOut P (u η) < P.numSets then
        (if idxOfOut P (u η) = i.val then 1 else 0) else loopVal u i k (insert η Tr)) /
      ((Finset.univ \ Tr).card : ℝ≥0∞)

lemma loop_eq (u : Nonce P → BitVec P.hashBits) (x : S.graph.Assignment) (m : Message P)
    (i : Fin P.numSets) (k : ℕ) (Tr : Finset (Nonce P)) :
    (∑ η : Nonce P, if idxOfOut P (u η) = i.val then
      Pr[= some (η, S.graph.encode (S.sets i) x) | simulateQ (signImpl P u) (S.signLoop x m k Tr)]
      else 0) = loopVal u i k Tr := by
  induction k generalizing Tr with
  | zero => simp [Scheme.signLoop, loopVal]
  | succ k ih =>
    by_cases hc : 0 < (Finset.univ \ Tr).card
    · rw [Scheme.signLoop, dif_pos hc]
      simp only [simulateQ_bind, simulateQ_unif, simulateQ_index, pure_bind]
      simp only [probOutput_bind_eq_sum_fintype, ProbComp.probOutput_uniformFin]
      have hcast : (Finset.univ \ Tr).card - 1 + 1 = (Finset.univ \ Tr).card := by omega
      have hcR : (((Finset.univ \ Tr).card - 1 : ℕ) : ℝ≥0∞) + 1 = ((Finset.univ \ Tr).card : ℝ≥0∞) := by
        rw [← Nat.cast_add_one, hcast]
      simp only [hcR]
      have key : ∀ z : Option (Signature P), ∑ j : Fin ((Finset.univ \ Tr).card - 1 + 1), ((Finset.univ \ Tr).card : ℝ≥0∞)⁻¹ *
          Pr[= z | simulateQ (signImpl P u)
            (if hi : idxOfOut P (u ((Finset.univ \ Tr).equivFin.symm (Fin.cast hcast j)).1)
                < P.numSets then
              pure (some (((Finset.univ \ Tr).equivFin.symm (Fin.cast hcast j)).1,
                S.graph.encode (S.sets ⟨idxOfOut P
                  (u ((Finset.univ \ Tr).equivFin.symm (Fin.cast hcast j)).1), hi⟩) x))
            else S.signLoop x m k
              (insert ((Finset.univ \ Tr).equivFin.symm (Fin.cast hcast j)).1 Tr))] =
          ∑ η ∈ Finset.univ \ Tr, ((Finset.univ \ Tr).card : ℝ≥0∞)⁻¹ *
          Pr[= z | simulateQ (signImpl P u)
            (if hi : idxOfOut P (u η) < P.numSets then
              pure (some (η, S.graph.encode (S.sets ⟨idxOfOut P (u η), hi⟩) x))
            else S.signLoop x m k (insert η Tr))] := fun z =>
        sum_fin_equivFin hcast (fun η => ((Finset.univ \ Tr).card : ℝ≥0∞)⁻¹ *
          Pr[= z | simulateQ (signImpl P u)
            (if hi : idxOfOut P (u η) < P.numSets then
              pure (some (η, S.graph.encode (S.sets ⟨idxOfOut P (u η), hi⟩) x))
            else S.signLoop x m k (insert η Tr))])
      simp only [key]
      simp only [sum_ite_sum_mul]
      rw [loopVal, ENNReal.div_eq_inv_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun η hη => ?_
      congr 1
      by_cases hi : idxOfOut P (u η) < P.numSets
      · rw [if_pos hi]
        simp only [dif_pos hi, simulateQ_pure, probOutput_pure]
        rw [Finset.sum_eq_single η]
        · by_cases h : idxOfOut P (u η) = i.val
          · have : (⟨idxOfOut P (u η), hi⟩ : Fin P.numSets) = i := Fin.ext h
            simp [this]
          · simp [h]
        · intro η' _ hne
          simp only [Option.some.injEq, Prod.mk.injEq]
          split_ifs <;> simp_all
        · simp
      · rw [if_neg hi]
        simp only [dif_neg hi]
        exact ih _
    · have : Finset.univ \ Tr = ∅ := by
        rw [← Finset.card_eq_zero]; omega
      rw [Scheme.signLoop, dif_neg hc]
      simp [loopVal, this]

lemma loopVal_update (u : Nonce P → BitVec P.hashBits) (i : Fin P.numSets) (a : Nonce P)
    (b : BitVec P.hashBits) (k : ℕ) (Tr : Finset (Nonce P)) (ha : a ∈ Tr) :
    loopVal (Function.update u a b) i k Tr = loopVal u i k Tr := by
  induction k generalizing Tr with
  | zero => simp [loopVal]
  | succ k ih =>
    simp only [loopVal]
    congr 1
    refine Finset.sum_congr rfl fun η hη => ?_
    have hne : η ≠ a := fun h => (Finset.mem_sdiff.1 hη).2 (h ▸ ha)
    rw [Function.update_of_ne hne, ih _ (Finset.mem_insert_of_mem ha)]

/-- Averaging a function that does not depend on one coordinate against a weight on that
coordinate. -/
lemma card_mul_sum_indep {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] (a : α)
    (q : β → ℝ≥0∞) (F : (α → β) → ℝ≥0∞) (hF : ∀ u b, F (Function.update u a b) = F u) :
    (Fintype.card β : ℝ≥0∞) * ∑ u, q (u a) * F u = (∑ b, q b) * ∑ u, F u := by
  let e := Equiv.funSplitAt a β
  have hsum : ∀ G : (α → β) → ℝ≥0∞, ∑ u, G u = ∑ b, ∑ r, G (e.symm (b, r)) := by
    intro G
    rw [← Equiv.sum_comp e.symm, Fintype.sum_prod_type]
  have happ : ∀ b r, e.symm (b, r) a = b := by
    intro b r; simp [e, Equiv.funSplitAt, Equiv.piSplitAt]
  have hT : ∀ b b' r, F (e.symm (b, r)) = F (e.symm (b', r)) := by
    intro b b' r
    have : e.symm (b, r) = Function.update (e.symm (b', r)) a b := by
      funext j
      by_cases hj : j = a
      · subst hj; simp [happ]
      · rw [Function.update_of_ne hj]
        simp [e, Equiv.funSplitAt, Equiv.piSplitAt, hj]
    rw [this, hF]
  rw [hsum, hsum]
  simp only [happ]
  have hc : (Fintype.card β : ℝ≥0∞) = ∑ _b : β, (1 : ℝ≥0∞) := by simp
  rw [hc, Finset.sum_mul, Finset.sum_mul]
  simp_rw [one_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ =>
    Finset.sum_congr rfl fun r _ => ?_
  rw [hT b b' r]

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
    rw [Nat.mul_add_mod', Nat.mod_eq_of_lt (Finset.mem_range.1 hr)]

lemma sum_idxOfOut (hidx : P.idxBits ≤ P.hashBits) (G : ℕ → ℝ≥0∞) :
    ∑ y : BitVec P.hashBits, G (idxOfOut P y) =
      (2 ^ (P.hashBits - P.idxBits) : ℕ) * ∑ r ∈ Finset.range (2 ^ P.idxBits), G r := by
  have hH : 2 ^ P.hashBits = 2 ^ (P.hashBits - P.idxBits) * 2 ^ P.idxBits := by
    rw [← pow_add, Nat.sub_add_cancel hidx]
  simp only [idxOfOut, BitVec.toNat_setWidth]
  rw [sum_bitVec_toNat (fun j => G (j % 2 ^ P.idxBits)), hH, sum_range_mul_mod]

/-- The closed form of the success probability with `k` trials, in reals. -/
def gR (P : Params) (k : ℕ) : ℝ := (1 - (1 - (P.numSets : ℝ) / 2 ^ P.idxBits) ^ k) / P.numSets

lemma q_nonneg (hM : P.numSets ≤ 2 ^ P.idxBits) : 0 ≤ 1 - (P.numSets : ℝ) / 2 ^ P.idxBits := by
  have hN : (0 : ℝ) < 2 ^ P.idxBits := by positivity
  have : (P.numSets : ℝ) ≤ 2 ^ P.idxBits := by exact_mod_cast hM
  rw [sub_nonneg, div_le_one hN]; exact this

lemma gR_nonneg (hM : P.numSets ≤ 2 ^ P.idxBits) (k : ℕ) : 0 ≤ gR P k := by
  unfold gR
  have hq := q_nonneg hM
  have hq1 : 1 - (P.numSets : ℝ) / 2 ^ P.idxBits ≤ 1 := by
    have : 0 ≤ (P.numSets : ℝ) / 2 ^ P.idxBits := by positivity
    linarith
  have : (1 - (P.numSets : ℝ) / 2 ^ P.idxBits) ^ k ≤ 1 := pow_le_one₀ hq hq1
  apply div_nonneg _ (Nat.cast_nonneg _)
  linarith

lemma gR_succ (hM0 : 0 < P.numSets) (hM : P.numSets ≤ 2 ^ P.idxBits) (k : ℕ) :
    ((2 ^ P.idxBits : ℕ) : ℝ≥0∞) * ENNReal.ofReal (gR P (k + 1)) =
      1 + ((2 ^ P.idxBits - P.numSets : ℕ) : ℝ≥0∞) * ENNReal.ofReal (gR P k) := by
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_natCast (2 ^ P.idxBits - P.numSets),
    ← ENNReal.ofReal_mul (Nat.cast_nonneg _), ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
    ← ENNReal.ofReal_one,
    ← ENNReal.ofReal_add zero_le_one (mul_nonneg (Nat.cast_nonneg _) (gR_nonneg hM k))]
  congr 1
  have hM0' : (0 : ℝ) < P.numSets := by exact_mod_cast hM0
  have hN : (0 : ℝ) < 2 ^ P.idxBits := by positivity
  rw [Nat.cast_sub hM]
  unfold gR
  push_cast
  generalize (2 : ℝ) ^ P.idxBits = N at hN ⊢
  generalize (P.numSets : ℝ) = M at hM0' ⊢
  have hN' : N ≠ 0 := hN.ne'
  have hM' : M ≠ 0 := hM0'.ne'
  have hq : N * (1 - M / N) = N - M := by field_simp
  rw [pow_succ]
  field_simp
  linear_combination (1 - M / N) ^ k * hq + M * (1 - M / N) ^ k * mul_inv_cancel₀ hN'

lemma card_bitVec_eq (n : ℕ) : Fintype.card (BitVec n) = 2 ^ n := by
  simp

lemma sum_loopVal (hidx : P.idxBits ≤ P.hashBits) (hM : P.numSets ≤ 2 ^ P.idxBits)
    (i : Fin P.numSets) (k : ℕ) (Tr : Finset (Nonce P)) (hk : Tr.card + k ≤ 2 ^ P.nonceBits) :
    ∑ u : Nonce P → BitVec P.hashBits, loopVal u i k Tr =
      (Fintype.card (Nonce P → BitVec P.hashBits) : ℝ≥0∞) * ENNReal.ofReal (gR P k) := by
  have hM0 : 0 < P.numSets := lt_of_le_of_lt (Nat.zero_le _) i.isLt
  induction k generalizing Tr with
  | zero => simp [loopVal, gR]
  | succ k ih =>
    set K := (Fintype.card (Nonce P → BitVec P.hashBits) : ℝ≥0∞) with hK
    have hcard : (Finset.univ \ Tr).card = 2 ^ P.nonceBits - Tr.card := by
      rw [Finset.card_univ_sdiff, card_bitVec_eq]
    have hc0 : ((Finset.univ \ Tr).card : ℝ≥0∞) ≠ 0 := by
      rw [hcard]; exact_mod_cast (by omega : 2 ^ P.nonceBits - Tr.card ≠ 0)
    have hct : ((Finset.univ \ Tr).card : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
    have per : ∀ η ∈ Finset.univ \ Tr,
        ∑ u : Nonce P → BitVec P.hashBits,
          (if idxOfOut P (u η) < P.numSets then
            (if idxOfOut P (u η) = i.val then (1 : ℝ≥0∞) else 0)
            else loopVal u i k (insert η Tr)) = K * ENNReal.ofReal (gR P (k + 1)) := by
      intro η hη
      have hηT : η ∉ Tr := (Finset.mem_sdiff.1 hη).2
      let qA : BitVec P.hashBits → ℝ≥0∞ := fun y =>
        if idxOfOut P y < P.numSets then (if idxOfOut P y = i.val then 1 else 0) else 0
      let qB : BitVec P.hashBits → ℝ≥0∞ := fun y => if idxOfOut P y < P.numSets then 0 else 1
      have hbody : ∀ u : Nonce P → BitVec P.hashBits,
          (if idxOfOut P (u η) < P.numSets then
            (if idxOfOut P (u η) = i.val then (1 : ℝ≥0∞) else 0)
            else loopVal u i k (insert η Tr)) =
          qA (u η) * 1 + qB (u η) * loopVal u i k (insert η Tr) := by
        intro u
        simp only [qA, qB]
        split_ifs <;> simp
      simp only [hbody]
      rw [Finset.sum_add_distrib]
      have hH0 : (Fintype.card (BitVec P.hashBits) : ℝ≥0∞) ≠ 0 := by
        rw [card_bitVec_eq]; exact_mod_cast (by positivity : 2 ^ P.hashBits ≠ 0)
      have hHt : (Fintype.card (BitVec P.hashBits) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
      rw [← ENNReal.mul_right_inj hH0 hHt, mul_add,
        card_mul_sum_indep η qA (fun _ => 1) (fun _ _ => rfl),
        card_mul_sum_indep η qB (fun u => loopVal u i k (insert η Tr))
          (fun u b => loopVal_update u i η b k _ (Finset.mem_insert_self _ _))]
      have hins : (insert η Tr).card + k ≤ 2 ^ P.nonceBits := by
        rw [Finset.card_insert_of_notMem hηT]; omega
      rw [ih _ hins]
      have hA : ∑ b, qA b = ((2 ^ (P.hashBits - P.idxBits) : ℕ) : ℝ≥0∞) := by
        rw [sum_idxOfOut hidx (fun r => if r < P.numSets then (if r = i.val then 1 else 0) else 0)]
        rw [Finset.sum_eq_single i.val]
        · simp
        · intro r _ hr; simp [hr]
        · intro h; exact absurd (Finset.mem_range.2 (lt_of_lt_of_le i.isLt hM)) h
      have hB : ∑ b, qB b = ((2 ^ (P.hashBits - P.idxBits) : ℕ) : ℝ≥0∞) *
          ((2 ^ P.idxBits - P.numSets : ℕ) : ℝ≥0∞) := by
        rw [sum_idxOfOut hidx (fun r => if r < P.numSets then 0 else 1)]
        congr 1
        rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, nsmul_one]
        congr 1
        rw [← Nat.card_Ico]
        congr 1
        ext r; simp; omega
      have hHc : (Fintype.card (BitVec P.hashBits) : ℝ≥0∞) =
          ((2 ^ (P.hashBits - P.idxBits) : ℕ) : ℝ≥0∞) * ((2 ^ P.idxBits : ℕ) : ℝ≥0∞) := by
        rw [card_bitVec_eq, ← Nat.cast_mul, ← pow_add, Nat.sub_add_cancel hidx]
      rw [hA, hB, hHc, Finset.sum_const, Finset.card_univ, nsmul_one, ← hK]
      symm
      calc ((2 ^ (P.hashBits - P.idxBits) : ℕ) : ℝ≥0∞) * ((2 ^ P.idxBits : ℕ) : ℝ≥0∞) *
            (K * ENNReal.ofReal (gR P (k + 1)))
          = ((2 ^ (P.hashBits - P.idxBits) : ℕ) : ℝ≥0∞) * K *
            (((2 ^ P.idxBits : ℕ) : ℝ≥0∞) * ENNReal.ofReal (gR P (k + 1))) := by ring
        _ = _ := by rw [gR_succ hM0 hM]; ring
    simp only [loopVal, ENNReal.div_eq_inv_mul]
    rw [← Finset.mul_sum, Finset.sum_comm, Finset.sum_congr rfl per, Finset.sum_const,
      nsmul_eq_mul, ← mul_assoc, ENNReal.inv_mul_cancel hc0 hct, one_mul]

theorem sum_signProb (x : S.graph.Assignment) (i : Fin P.numSets)
    (hL : P.trialLimit ≤ 2 ^ P.nonceBits) (hM : P.numSets ≤ 2 ^ P.idxBits)
    (hidx : P.idxBits ≤ P.hashBits) :
    (∑ u : Nonce P → BitVec P.hashBits, signProb S u x i) /
        (Fintype.card (Nonce P → BitVec P.hashBits) : ℝ≥0∞) =
      (1 - (1 - (P.numSets : ℝ≥0∞) / 2 ^ P.idxBits) ^ P.trialLimit) / P.numSets := by
  have hM0 : 0 < P.numSets := lt_of_le_of_lt (Nat.zero_le _) i.isLt
  have h1 : ∀ u, signProb S u x i = loopVal u i P.trialLimit ∅ := fun u =>
    loop_eq S u x (Attack.msg₁ P) i P.trialLimit ∅
  simp only [h1]
  rw [sum_loopVal hidx hM i P.trialLimit ∅ (by simpa using hL)]
  have hK0 : (Fintype.card (Nonce P → BitVec P.hashBits) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos.ne' : Fintype.card (Nonce P → BitVec P.hashBits) ≠ 0)
  rw [mul_comm, mul_div_assoc, ENNReal.div_self hK0 (ENNReal.natCast_ne_top _), mul_one]
  have hN : (0 : ℝ) < 2 ^ P.idxBits := by positivity
  have hM0' : (0 : ℝ) < P.numSets := by exact_mod_cast hM0
  unfold gR
  rw [ENNReal.ofReal_div_of_pos hM0', ENNReal.ofReal_natCast,
    ENNReal.ofReal_sub _ (pow_nonneg (q_nonneg hM) _), ENNReal.ofReal_one,
    ENNReal.ofReal_pow (q_nonneg hM), ENNReal.ofReal_sub _ (by positivity), ENNReal.ofReal_one,
    ENNReal.ofReal_div_of_pos hN, ENNReal.ofReal_natCast]
  congr
  rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_pow (by norm_num)]

end Analysis

end OptimalOTS
