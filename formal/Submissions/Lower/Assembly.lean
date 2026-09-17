import Submissions.Lower.Ranks
import Submissions.Lower.LazyEager
import Submissions.Lower.Numerics
import Submissions.Lower.NumericsSuccess
import Submissions.Lower.Cells
import Submissions.Lower.Sign
import Submissions.Lower.Nonce
import Submissions.Lower.Product
import Submissions.Lower.TailBound
import Submissions.Lower.RankIntegral
import Submissions.Lower.AvgSucc
import Submissions.Lower.Decomp
import OptimalOTS.Statement

/-!
# Assembling the probability bound

Combining the lazy-to-eager step, the unrolled experiment, the table factorization, the
signing and nonce-search distributions, and the averaged construction bound, the attack with
`q = 2^110` construction attempts and `T = 5 · 2^120` nonce trials forges with probability
above `3/32` against every scheme whose signatures verify within 24 compressions.
-/

open OracleSpec OracleComp ENNReal

noncomputable section

open scoped Classical

namespace OptimalOTS

namespace Assembly

open Analysis Attack


/-- The summand of the unrolled experiment for graph tables `t` and nonce tables `u`, `w`. -/
def Fsum {P : Params} (S : Scheme P) (q T : ℕ) (t : S.graph.Tab)
    (u w : Nonce P → BitVec P.hashBits) : ℝ≥0∞ :=
  (∑ z : S.graph.Assignment, ∑ i : Fin P.numSets,
    signProb S u (S.graph.evalTab z t) i *
      ∑ ℓ ∈ Finset.range 450,
        (if bestPure P T (rkOf S i (obsCands S i (S.graph.recOf z t))) w = some ℓ then 1 else 0) *
          ENNReal.ofReal (succ S q i ℓ z t)) / (Fintype.card S.graph.Assignment : ℝ≥0∞)

theorem bitVec_zero_ne_one {w : ℕ} (hw : 0 < w) : (0 : BitVec w) ≠ 1 := by
  intro h
  have := congrArg (fun x : BitVec w => x.getLsbD 0) h
  simp [BitVec.getLsbD_one, hw] at this

theorem msg₁_ne_msg₂ : Attack.msg₁ paperParams ≠ Attack.msg₂ paperParams :=
  bitVec_zero_ne_one (w := 256) (by norm_num)

theorem paperParams_numSets : paperParams.numSets = 2 ^ 115 := rfl
theorem paperParams_idxBits : paperParams.idxBits = 128 := rfl
theorem paperParams_trialLimit : paperParams.trialLimit = 2 ^ 21 := rfl
theorem paperParams_securityBits : paperParams.securityBits = 127 := rfl

theorem paperParams_numSets_pos : 0 < paperParams.numSets := by
  rw [paperParams_numSets]; positivity

/-- Averages do not depend on the `Fintype` instance. -/
theorem avg_inst_congr {α : Type*} (i₁ i₂ : Fintype α) (f : α → ℝ≥0∞) :
    (∑ x ∈ @Finset.univ α i₁, f x) / (@Fintype.card α i₁ : ℝ≥0∞) =
      (∑ x ∈ @Finset.univ α i₂, f x) / (@Fintype.card α i₂ : ℝ≥0∞) := by
  obtain rfl : i₁ = i₂ := Subsingleton.elim _ _
  rfl

/-- Moving the last of four nested sums to the front. -/
theorem sum_comm_last {α β γ δ M : Type*} [AddCommMonoid M] (s₁ : Finset α) (s₂ : Finset β)
    (s₃ : Finset γ) (s₄ : Finset δ) (f : α → β → γ → δ → M) :
    ∑ a ∈ s₁, ∑ b ∈ s₂, ∑ c ∈ s₃, ∑ d ∈ s₄, f a b c d =
      ∑ d ∈ s₄, ∑ a ∈ s₁, ∑ b ∈ s₂, ∑ c ∈ s₃, f a b c d := by
  calc ∑ a ∈ s₁, ∑ b ∈ s₂, ∑ c ∈ s₃, ∑ d ∈ s₄, f a b c d
      = ∑ a ∈ s₁, ∑ b ∈ s₂, ∑ d ∈ s₄, ∑ c ∈ s₃, f a b c d :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ a ∈ s₁, ∑ d ∈ s₄, ∑ b ∈ s₂, ∑ c ∈ s₃, f a b c d :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = _ := Finset.sum_comm

theorem sum_Fsum_le_probTrue (S : Scheme paperParams) (q T : ℕ) :
    (∑ t, ∑ u, ∑ w, Fsum S q T t u w) /
        ((Fintype.card S.graph.Tab : ℝ≥0∞) *
          Fintype.card (Nonce paperParams → BitVec paperParams.hashBits) *
          Fintype.card (Nonce paperParams → BitVec paperParams.hashBits)) ≤
      probTrue paperParams (experiment S (adversary S q T)) := by
  rw [← sum_table_eq S msg₁_ne_msg₂ (Fsum S q T)]
  unfold probTrue
  rw [probOutput_oracleImpl_eq_sum_table (decode S) (decode_injective S) _ (hashQueriesIn_experiment S q T) true]
  refine (le_of_eq ?_).trans (ENNReal.div_le_div_right
    (Finset.sum_le_sum fun g _ => sum_le_probOutput_table S q T msg₁_ne_msg₂ g) _)
  exact avg_inst_congr _ _ _

/-- Swapping two pairs of nested sums. -/
theorem sum_comm_pairs {α β γ δ : Type*} (s₁ : Finset α) (s₂ : Finset β) (s₃ : Finset γ)
    (s₄ : Finset δ) (f : α → β → γ → δ → ℝ≥0∞) :
    ∑ a ∈ s₁, ∑ b ∈ s₂, ∑ c ∈ s₃, ∑ d ∈ s₄, f a b c d =
      ∑ c ∈ s₃, ∑ d ∈ s₄, ∑ a ∈ s₁, ∑ b ∈ s₂, f a b c d := by
  calc ∑ a ∈ s₁, ∑ b ∈ s₂, ∑ c ∈ s₃, ∑ d ∈ s₄, f a b c d
      = ∑ a ∈ s₁, ∑ c ∈ s₃, ∑ b ∈ s₂, ∑ d ∈ s₄, f a b c d :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ a ∈ s₁, ∑ c ∈ s₃, ∑ d ∈ s₄, ∑ b ∈ s₂, f a b c d :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ c ∈ s₃, ∑ a ∈ s₁, ∑ d ∈ s₄, ∑ b ∈ s₂, f a b c d := Finset.sum_comm
    _ = ∑ c ∈ s₃, ∑ d ∈ s₄, ∑ a ∈ s₁, ∑ b ∈ s₂, f a b c d :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm

/-- The nonce tables. -/
abbrev NTab := Nonce paperParams → BitVec paperParams.hashBits

/-- Signing selects each index with this probability. -/
def sigma : ℝ≥0∞ :=
  (1 - (1 - (paperParams.numSets : ℝ≥0∞) / 2 ^ paperParams.idxBits) ^ paperParams.trialLimit) /
    paperParams.numSets

/-- The nonce search finds rank `ℓ` with this probability. -/
def omegaR (ℓ : ℕ) : ℝ :=
  (1 - (ℓ : ℝ) / 2 ^ paperParams.idxBits) ^ Numerics.T -
    (1 - ((ℓ : ℝ) + 1) / 2 ^ paperParams.idxBits) ^ Numerics.T

theorem card_NTab_ne_zero : (Fintype.card NTab : ℝ≥0∞) ≠ 0 := by
  exact_mod_cast (Fintype.card_ne_zero : Fintype.card NTab ≠ 0)

theorem card_NTab_ne_top : (Fintype.card NTab : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _

theorem sum_signProb_eq (S : Scheme paperParams) (x : S.graph.Assignment)
    (i : Fin paperParams.numSets) :
    ∑ u : NTab, signProb S u x i = Fintype.card NTab * sigma := by
  have h := sum_signProb S x i (by decide) (by decide) (by decide)
  exact ((ENNReal.eq_div_iff card_NTab_ne_zero card_NTab_ne_top).mp h.symm).symm

theorem sum_bestPure_ite (S : Scheme paperParams) (i : Fin paperParams.numSets)
    (C : Finset S.graph.Rec) (ℓ : ℕ) (hℓ : ℓ < 450) :
    ∑ w : NTab, (if bestPure paperParams Numerics.T (rkOf S i C) w = some ℓ then (1 : ℝ≥0∞)
      else 0) = Fintype.card NTab * ENNReal.ofReal (omegaR ℓ) := by
  have h := sum_bestPure_eq (P := paperParams) Numerics.T (by decide) (by decide) (rkOf S i C) 450
    (fun ℓ hℓ => rkOf_existsUnique S i C (by decide) hℓ (lt_of_lt_of_le hℓ (by decide)))
    (fun n ℓ h => rkOf_lt S i C h) ℓ hℓ
  exact ((ENNReal.eq_div_iff card_NTab_ne_zero card_NTab_ne_top).mp h.symm).symm

theorem sum_factor {U W L : Type*} [Fintype U] [Fintype W] (sL : Finset L)
    (a : U → ℝ≥0∞) (b : W → L → ℝ≥0∞) (c : L → ℝ≥0∞) (k : ℝ≥0∞) :
    ∑ u, ∑ w, (a u * ∑ ℓ ∈ sL, b w ℓ * c ℓ) * k =
      (∑ u, a u) * (∑ ℓ ∈ sL, (∑ w, b w ℓ) * c ℓ) * k := by
  rw [Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [← Finset.sum_mul, ← Finset.mul_sum]
  congr 2
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun ℓ _ => (Finset.sum_mul _ _ _).symm

theorem sum_sum_Fsum {P : Params} (S : Scheme P) (q T : ℕ) (t : S.graph.Tab) (σ cU : ℝ≥0∞)
    (ω : ℕ → ℝ)
    (hsign : ∀ x i, ∑ u : Nonce P → BitVec P.hashBits, signProb S u x i = cU * σ)
    (hnonce : ∀ i C, ∀ ℓ ∈ Finset.range 450,
      ∑ w : Nonce P → BitVec P.hashBits,
        (if bestPure P T (rkOf S i C) w = some ℓ then (1 : ℝ≥0∞) else 0) =
          cU * ENNReal.ofReal (ω ℓ)) :
    ∑ u : Nonce P → BitVec P.hashBits, ∑ w : Nonce P → BitVec P.hashBits, Fsum S q T t u w =
      ∑ z : S.graph.Assignment, ∑ i : Fin P.numSets,
        (cU * σ) * (∑ ℓ ∈ Finset.range 450,
          (cU * ENNReal.ofReal (ω ℓ)) * ENNReal.ofReal (succ S q i ℓ z t)) *
        (Fintype.card S.graph.Assignment : ℝ≥0∞)⁻¹ := by
  unfold Fsum
  simp only [div_eq_mul_inv, Finset.sum_mul]
  rw [sum_comm_pairs]
  refine Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun i _ => ?_
  rw [sum_factor, hsign]
  congr 2
  exact Finset.sum_congr rfl fun ℓ hℓ => by rw [hnonce i _ ℓ hℓ]

/-- `ofReal` of a sum is at most the sum of `ofReal`s. -/
theorem ofReal_sum_le {α : Type*} (s : Finset α) (f : α → ℝ) :
    ENNReal.ofReal (∑ a ∈ s, f a) ≤ ∑ a ∈ s, ENNReal.ofReal (f a) := by
  let _ : DecidableEq α := Classical.decEq α
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (ENNReal.ofReal_add_le).trans (add_le_add le_rfl ih)

theorem omegaR_nonneg (ℓ : ℕ) (hℓ : ℓ < 450) : 0 ≤ omegaR ℓ := by
  unfold omegaR
  have hN : (2 : ℝ) ^ paperParams.idxBits = 2 ^ 128 := rfl
  rw [hN]
  have hℓ' : (ℓ : ℝ) + 1 ≤ 450 := by exact_mod_cast hℓ
  have h128 : (450 : ℝ) ≤ 2 ^ 128 := by norm_num
  have hpos : (0 : ℝ) < 2 ^ 128 := by positivity
  have h0 : 0 ≤ 1 - ((ℓ : ℝ) + 1) / 2 ^ 128 := by
    rw [sub_nonneg, div_le_one hpos]; linarith
  have hle : 1 - ((ℓ : ℝ) + 1) / 2 ^ 128 ≤ 1 - (ℓ : ℝ) / 2 ^ 128 := by
    have : (ℓ : ℝ) / 2 ^ 128 ≤ ((ℓ : ℝ) + 1) / 2 ^ 128 :=
      div_le_div_of_nonneg_right (by linarith) hpos.le
    linarith
  exact sub_nonneg.mpr (pow_le_pow_left₀ h0 hle _)

theorem sum_succ_ge (S : Scheme paperParams) (hcost : ∀ i, S.verifyCost i ≤ 24) (ℓ : ℕ)
    (hℓ : ℓ < 450) :
    (paperParams.numSets : ℝ) * Fintype.card S.graph.Assignment * Fintype.card S.graph.Tab *
        Numerics.rankSuccess (ℓ + 1) ≤
      ∑ t : S.graph.Tab, ∑ z : S.graph.Assignment, ∑ i : Fin paperParams.numSets,
        succ S Numerics.q i ℓ z t := by
  have hre : ∑ t : S.graph.Tab, ∑ z : S.graph.Assignment, ∑ i : Fin paperParams.numSets,
      succ S Numerics.q i ℓ z t =
      ∑ i : Fin paperParams.numSets, ∑ z : S.graph.Assignment, ∑ t : S.graph.Tab,
      succ S Numerics.q i ℓ z t := by
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl fun z _ => Finset.sum_comm]
    rw [Finset.sum_comm]
  rw [hre]
  rcases Nat.eq_zero_or_pos ℓ with rfl | hℓ₁
  · have h1 : ∀ i z t, succ S Numerics.q i 0 z t = 1 := by
      intro i z t
      simp [succ, rankElem_zero]
    simp only [h1, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    have : Numerics.rankSuccess (0 + 1) = 1 := by simp [Numerics.rankSuccess]
    rw [this, Fintype.card_fin]
    push_cast
    nlinarith [show (0 : ℝ) ≤ ((Fintype.card S.graph.Assignment : ℕ) : ℝ) by positivity,
      show (0 : ℝ) ≤ ((Fintype.card S.graph.Tab : ℕ) : ℝ) by positivity]
  · have hZ : (0 : ℝ) < ((Fintype.card S.graph.Assignment : ℕ) : ℝ) := by positivity
    have hTb : (0 : ℝ) < ((Fintype.card S.graph.Tab : ℕ) : ℝ) := by positivity
    have hRc : (0 : ℝ) < ((Fintype.card S.graph.Rec : ℕ) : ℝ) := by positivity
    have hper : ∀ i : Fin paperParams.numSets,
        (∑ ξ : S.graph.Rec, max 0 (1 - D S i ℓ ξ / 113)) /
            ((Fintype.card S.graph.Rec : ℕ) : ℝ) *
          (((Fintype.card S.graph.Assignment : ℕ) : ℝ) * ((Fintype.card S.graph.Tab : ℕ) : ℝ)) ≤
          ∑ z : S.graph.Assignment, ∑ t : S.graph.Tab, succ S Numerics.q i ℓ z t := by
      intro i
      have h := avg_D_le_avg_succ S i ℓ
      exact (le_div_iff₀ (mul_pos hZ hTb)).mp h
    have htail' : ∀ d : ℝ, 0 < d → d ≤ 113 →
        511 / 512 - (ℓ : ℝ) / 500 * (113 / d) ^ 21 ≤
          ((Finset.univ.filter fun p : Fin paperParams.numSets × S.graph.Rec =>
              D S p.1 ℓ p.2 < d).card : ℝ) /
            ((Fintype.card (Fin paperParams.numSets × S.graph.Rec) : ℕ) : ℝ) := by
      intro d hd hd'
      have h := tail_bound S hcost ℓ hℓ d hd hd'
      rwa [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
    have hne : Nonempty (Fin paperParams.numSets × S.graph.Rec) :=
      ⟨(⟨0, paperParams_numSets_pos⟩, Classical.arbitrary _)⟩
    have hint := rankSuccess_le_avg_of_tail (ι := Fin paperParams.numSets × S.graph.Rec)
      (fun p => D S p.1 ℓ p.2) (fun p => targetWeight_nonneg S _ _ _) ℓ hℓ₁ hℓ htail'
    have hM : (0 : ℝ) < (paperParams.numSets : ℝ) := by
      exact_mod_cast paperParams_numSets_pos
    rw [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul,
      le_div_iff₀ (mul_pos hM hRc), Fintype.sum_prod_type] at hint
    calc (paperParams.numSets : ℝ) * ((Fintype.card S.graph.Assignment : ℕ) : ℝ) *
          ((Fintype.card S.graph.Tab : ℕ) : ℝ) * Numerics.rankSuccess (ℓ + 1)
        = (Numerics.rankSuccess (ℓ + 1) * ((paperParams.numSets : ℝ) *
            ((Fintype.card S.graph.Rec : ℕ) : ℝ))) / ((Fintype.card S.graph.Rec : ℕ) : ℝ) *
            (((Fintype.card S.graph.Assignment : ℕ) : ℝ) *
              ((Fintype.card S.graph.Tab : ℕ) : ℝ)) := by
          field_simp
      _ ≤ (∑ i : Fin paperParams.numSets, ∑ ξ : S.graph.Rec, max 0 (1 - D S i ℓ ξ / 113)) /
            ((Fintype.card S.graph.Rec : ℕ) : ℝ) *
            (((Fintype.card S.graph.Assignment : ℕ) : ℝ) *
              ((Fintype.card S.graph.Tab : ℕ) : ℝ)) := by
          gcongr
      _ = ∑ i : Fin paperParams.numSets,
            (∑ ξ : S.graph.Rec, max 0 (1 - D S i ℓ ξ / 113)) /
              ((Fintype.card S.graph.Rec : ℕ) : ℝ) *
              (((Fintype.card S.graph.Assignment : ℕ) : ℝ) *
                ((Fintype.card S.graph.Tab : ℕ) : ℝ)) := by
          rw [Finset.sum_div, Finset.sum_mul]
      _ ≤ _ := Finset.sum_le_sum fun i _ => hper i

theorem mul_div_cancel_left' (c a : ℝ≥0∞) (h0 : c ≠ 0) (ht : c ≠ ⊤) : c * a / c = a := by
  have := ENNReal.mul_div_mul_left a 1 h0 ht
  rwa [mul_one, div_one] at this

theorem ofReal_sum3_le {α β γ : Type*} [Fintype α] [Fintype β] (s : Finset γ)
    (f : α → β → γ → ℝ) :
    ENNReal.ofReal (∑ a, ∑ b, ∑ c ∈ s, f a b c) ≤ ∑ a, ∑ b, ∑ c ∈ s, ENNReal.ofReal (f a b c) :=
  (ofReal_sum_le _ _).trans <| Finset.sum_le_sum fun a _ =>
    (ofReal_sum_le _ _).trans <| Finset.sum_le_sum fun b _ => ofReal_sum_le _ _

/-- The average forging success, as a real number. -/
def successR : ℝ := ∑ ℓ ∈ Finset.range 450, omegaR ℓ * Numerics.rankSuccess (ℓ + 1)

theorem sum_Fsum_ge (S : Scheme paperParams) (hcost : ∀ i, S.verifyCost i ≤ 24) :
    (Fintype.card S.graph.Tab : ℝ≥0∞) * Fintype.card NTab * Fintype.card NTab *
        (sigma * ENNReal.ofReal ((paperParams.numSets : ℝ) * successR)) ≤
      ∑ t, ∑ u : NTab, ∑ w : NTab, Fsum S Numerics.q Numerics.T t u w := by
  have hZ0 : (Fintype.card S.graph.Assignment : ℝ≥0∞) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hZt : (Fintype.card S.graph.Assignment : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hrew : ∀ t, ∑ u : NTab, ∑ w : NTab, Fsum S Numerics.q Numerics.T t u w =
      ∑ z : S.graph.Assignment, ∑ i : Fin paperParams.numSets,
        ((Fintype.card NTab : ℝ≥0∞) * sigma) * (∑ ℓ ∈ Finset.range 450,
          ((Fintype.card NTab : ℝ≥0∞) * ENNReal.ofReal (omegaR ℓ)) * ENNReal.ofReal (succ S Numerics.q i ℓ z t)) * (Fintype.card S.graph.Assignment : ℝ≥0∞)⁻¹ :=
    fun t => sum_sum_Fsum S Numerics.q Numerics.T t sigma _ omegaR
      (fun x i => sum_signProb_eq S x i) (fun i C ℓ hℓ => sum_bestPure_ite S i C ℓ
        (Finset.mem_range.mp hℓ))
  simp only [hrew]
  have hterm : ∀ t z i,
      ((Fintype.card NTab : ℝ≥0∞) * sigma) * (∑ ℓ ∈ Finset.range 450,
          ((Fintype.card NTab : ℝ≥0∞) * ENNReal.ofReal (omegaR ℓ)) * ENNReal.ofReal (succ S Numerics.q i ℓ z t)) * (Fintype.card S.graph.Assignment : ℝ≥0∞)⁻¹ =
        ((Fintype.card NTab : ℝ≥0∞) * sigma * (Fintype.card NTab : ℝ≥0∞) * (Fintype.card S.graph.Assignment : ℝ≥0∞)⁻¹) * ∑ ℓ ∈ Finset.range 450,
          ENNReal.ofReal (omegaR ℓ * succ S Numerics.q i ℓ z t) := by
    intro t z i
    rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun ℓ hℓ => ?_
    rw [ENNReal.ofReal_mul (omegaR_nonneg ℓ (Finset.mem_range.mp hℓ))]
    ring
  simp only [hterm, ← Finset.mul_sum]
  have hreal : (paperParams.numSets : ℝ) * ((Fintype.card S.graph.Assignment : ℕ) : ℝ) *
        ((Fintype.card S.graph.Tab : ℕ) : ℝ) * successR ≤
      ∑ t : S.graph.Tab, ∑ z : S.graph.Assignment, ∑ i : Fin paperParams.numSets,
        ∑ ℓ ∈ Finset.range 450, omegaR ℓ * succ S Numerics.q i ℓ z t := by
    have hswap : ∑ t : S.graph.Tab, ∑ z : S.graph.Assignment, ∑ i : Fin paperParams.numSets,
        ∑ ℓ ∈ Finset.range 450, omegaR ℓ * succ S Numerics.q i ℓ z t =
        ∑ ℓ ∈ Finset.range 450, omegaR ℓ * ∑ t : S.graph.Tab, ∑ z : S.graph.Assignment,
          ∑ i : Fin paperParams.numSets, succ S Numerics.q i ℓ z t := by
      simp only [Finset.mul_sum]
      exact sum_comm_last _ _ _ _ _
    rw [hswap, successR, Finset.mul_sum]
    refine Finset.sum_le_sum fun ℓ hℓ => ?_
    have h := sum_succ_ge S hcost ℓ (Finset.mem_range.mp hℓ)
    have hω := omegaR_nonneg ℓ (Finset.mem_range.mp hℓ)
    nlinarith
  have e : ENNReal.ofReal ((paperParams.numSets : ℝ) *
        ((Fintype.card S.graph.Assignment : ℕ) : ℝ) * ((Fintype.card S.graph.Tab : ℕ) : ℝ) *
          successR) =
      (Fintype.card S.graph.Assignment : ℝ≥0∞) * ((Fintype.card S.graph.Tab : ℝ≥0∞) *
        ENNReal.ofReal ((paperParams.numSets : ℝ) * successR)) := by
    rw [show (paperParams.numSets : ℝ) * ((Fintype.card S.graph.Assignment : ℕ) : ℝ) *
        ((Fintype.card S.graph.Tab : ℕ) : ℝ) * successR =
        ((Fintype.card S.graph.Assignment : ℕ) : ℝ) * (((Fintype.card S.graph.Tab : ℕ) : ℝ) *
          ((paperParams.numSets : ℝ) * successR)) by ring]
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg (Fintype.card S.graph.Assignment)),
      ENNReal.ofReal_mul (Nat.cast_nonneg (Fintype.card S.graph.Tab)),
      ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]
  calc (Fintype.card S.graph.Tab : ℝ≥0∞) * (Fintype.card NTab : ℝ≥0∞) *
          (Fintype.card NTab : ℝ≥0∞) *
          (sigma * ENNReal.ofReal ((paperParams.numSets : ℝ) * successR))
      = ((Fintype.card NTab : ℝ≥0∞) * sigma * (Fintype.card NTab : ℝ≥0∞) *
          (Fintype.card S.graph.Assignment : ℝ≥0∞)⁻¹) *
          ENNReal.ofReal ((paperParams.numSets : ℝ) *
            ((Fintype.card S.graph.Assignment : ℕ) : ℝ) *
            ((Fintype.card S.graph.Tab : ℕ) : ℝ) * successR) := by
        rw [e]
        calc (Fintype.card S.graph.Tab : ℝ≥0∞) * (Fintype.card NTab : ℝ≥0∞) *
              (Fintype.card NTab : ℝ≥0∞) *
              (sigma * ENNReal.ofReal ((paperParams.numSets : ℝ) * successR))
            = ((Fintype.card S.graph.Tab : ℝ≥0∞) * (Fintype.card NTab : ℝ≥0∞) *
              (Fintype.card NTab : ℝ≥0∞) *
              (sigma * ENNReal.ofReal ((paperParams.numSets : ℝ) * successR))) *
              ((Fintype.card S.graph.Assignment : ℝ≥0∞)⁻¹ *
                (Fintype.card S.graph.Assignment : ℝ≥0∞)) := by
              rw [ENNReal.inv_mul_cancel hZ0 hZt, mul_one]
          _ = _ := by ring
    _ ≤ ((Fintype.card NTab : ℝ≥0∞) * sigma * (Fintype.card NTab : ℝ≥0∞) *
          (Fintype.card S.graph.Assignment : ℝ≥0∞)⁻¹) *
          ∑ t : S.graph.Tab, ∑ z : S.graph.Assignment, ∑ i : Fin paperParams.numSets,
            ∑ ℓ ∈ Finset.range 450, ENNReal.ofReal (omegaR ℓ * succ S Numerics.q i ℓ z t) := by
        gcongr
        refine le_trans (ENNReal.ofReal_le_ofReal hreal) ?_
        exact (ofReal_sum_le _ _).trans <| Finset.sum_le_sum fun t _ => ofReal_sum3_le _ _
    _ = _ := by simp only [Finset.mul_sum]

theorem one_sub_signFailure_nonneg : 0 ≤ 1 - Numerics.signFailure := by
  unfold Numerics.signFailure
  have h0 : 0 ≤ 1 - (2 : ℝ)⁻¹ ^ 13 := by norm_num
  have h1 : 1 - (2 : ℝ)⁻¹ ^ 13 ≤ 1 := by norm_num
  linarith [pow_le_one₀ h0 h1 (n := 2 ^ 21)]

theorem one_sub_sigma_eq :
    1 - (1 - (paperParams.numSets : ℝ≥0∞) / 2 ^ paperParams.idxBits) ^ paperParams.trialLimit =
      ENNReal.ofReal (1 - Numerics.signFailure) := by
  have hM : (paperParams.numSets : ℝ≥0∞) = ENNReal.ofReal ((2 : ℝ) ^ 115) := by
    rw [paperParams_numSets, Nat.cast_pow, Nat.cast_ofNat, ENNReal.ofReal_pow (by norm_num),
      ENNReal.ofReal_ofNat]
  have hN : (2 : ℝ≥0∞) ^ paperParams.idxBits = ENNReal.ofReal ((2 : ℝ) ^ 128) := by
    rw [paperParams_idxBits, ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]
  have hratio : (2 : ℝ) ^ 115 / 2 ^ 128 = (2 : ℝ)⁻¹ ^ 13 := by norm_num
  rw [hM, hN, ← ENNReal.ofReal_div_of_pos (by norm_num), hratio, paperParams_trialLimit]
  rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (by norm_num),
    ← ENNReal.ofReal_pow (by norm_num), ← ENNReal.ofReal_sub _ (by positivity)]
  rfl

theorem omegaR_eq (ℓ : ℕ) : omegaR ℓ = Numerics.omega (ℓ + 1) := by
  unfold omegaR Numerics.omega Numerics.N
  rw [paperParams_idxBits]
  simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right, Nat.cast_pow, Nat.cast_ofNat]

theorem successR_eq : successR =
    ∑ ℓ ∈ Finset.Icc 1 450, Numerics.omega ℓ * Numerics.rankSuccess ℓ := by
  unfold successR
  simp only [omegaR_eq]
  have hI : Finset.Icc 1 450 = Finset.Ico 1 451 :=
    Finset.ext fun x => by simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
  rw [hI, Finset.sum_Ico_eq_sum_range]
  exact Finset.sum_congr rfl fun ℓ _ => by rw [add_comm 1 ℓ]

theorem sigma_mul_eq :
    sigma * ENNReal.ofReal ((paperParams.numSets : ℝ) * successR) =
      ENNReal.ofReal ((1 - Numerics.signFailure) *
        ∑ ℓ ∈ Finset.Icc 1 450, Numerics.omega ℓ * Numerics.rankSuccess ℓ) := by
  have hM0 : (paperParams.numSets : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr paperParams_numSets_pos.ne'
  have hMt : (paperParams.numSets : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast, sigma, ← mul_assoc,
    ENNReal.div_mul_cancel hM0 hMt, one_sub_sigma_eq,
    ← ENNReal.ofReal_mul one_sub_signFailure_nonneg, successR_eq]

theorem probTrue_gt (S : Scheme paperParams) (hcost : ∀ i, S.verifyCost i ≤ 24) :
    ENNReal.ofReal (3 / 32) <
      probTrue paperParams (experiment S (adversary S Numerics.q Numerics.T)) := by
  have h1 := sum_Fsum_le_probTrue S Numerics.q Numerics.T
  have h2 := sum_Fsum_ge S hcost
  have hT0 : (Fintype.card S.graph.Tab : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hc0 : (Fintype.card S.graph.Tab : ℝ≥0∞) * Fintype.card NTab * Fintype.card NTab ≠ 0 :=
    mul_ne_zero (mul_ne_zero hT0 card_NTab_ne_zero) card_NTab_ne_zero
  have hct : (Fintype.card S.graph.Tab : ℝ≥0∞) * Fintype.card NTab * Fintype.card NTab ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) card_NTab_ne_top)
      card_NTab_ne_top
  have hcancel := mul_div_cancel_left'
    ((Fintype.card S.graph.Tab : ℝ≥0∞) * Fintype.card NTab * Fintype.card NTab)
    (sigma * ENNReal.ofReal ((paperParams.numSets : ℝ) * successR)) hc0 hct
  have h3 : sigma * ENNReal.ofReal ((paperParams.numSets : ℝ) * successR) ≤
      probTrue paperParams (experiment S (adversary S Numerics.q Numerics.T)) := by
    rw [← hcancel]
    exact (ENNReal.div_le_div_right h2 _).trans h1
  rw [sigma_mul_eq] at h3
  refine lt_of_lt_of_le ?_ h3
  exact (ENNReal.ofReal_lt_ofReal_iff (by linarith [Numerics.success_lt])).mpr Numerics.success_lt

end Assembly

end OptimalOTS
