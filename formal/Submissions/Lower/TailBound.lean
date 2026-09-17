import Submissions.Lower.AnalysisDefs
import OptimalOTS.Statement
import Submissions.Lower.Information
import Submissions.Lower.Counting
import Submissions.Lower.Numerics
import Submissions.Lower.Ranks

/-!
# The distribution of the weight at a given rank

For the parameters of the paper and a scheme whose signatures verify within 24 units, the target
of rank `ℓ` weighs less than `d` with probability at least `511/512 - ℓ/100 · (123/d)^22`, for a
uniform index and a uniform record.
-/

open OracleSpec OracleComp ENNReal

noncomputable section

open scoped Classical

namespace OptimalOTS

namespace Analysis

open Attack

lemma weight_eq_infoWeight (S : Scheme paperParams) (i : Fin paperParams.numSets)
    (ξ : S.graph.Rec) (g : Fin S.graph.size) :
    weight S i (obsCands S i ξ) g = infoWeight (evalHashAt S i) (reveal S i) ξ g := by
  unfold weight infoWeight obsCands
  rfl

lemma nodeCost_pos {P : Params} (G : Graph P) (v : Fin G.size) (hv : (G.kind v).IsHash) :
    1 ≤ G.nodeCost v := by
  unfold Graph.nodeCost
  split
  · exact le_max_left _ _
  · rename_i h
    match hk : G.kind v, hv with
    | .hash p hp τ hl, _ => exact (h p hp τ hl hk).elim

lemma card_targetSet_le (S : Scheme paperParams) (hcost : ∀ i, S.verifyCost i ≤ 24)
    (j : Fin paperParams.numSets) : (targetSet S j).card ≤ 22 := by
  have hroot : S.graph.root ∈ evalHashAt S j := by
    simp only [evalHashAt, Graph.evalHash, Graph.evaluated, Finset.mem_filter, Finset.mem_univ,
      true_and]
    exact ⟨⟨Graph.Visited.root, S.root_not_mem j⟩, S.graph.root_isHash⟩
  have h1 : (evalHashAt S j).card ≤ S.graph.reconstructCost (S.sets j) := by
    unfold Graph.reconstructCost
    calc (evalHashAt S j).card = ∑ _v ∈ evalHashAt S j, 1 := by simp
      _ ≤ ∑ v ∈ evalHashAt S j, S.graph.nodeCost v := by
          refine Finset.sum_le_sum fun v hv => nodeCost_pos _ _ ?_
          simp only [evalHashAt, Graph.evalHash, Finset.mem_filter] at hv
          exact hv.2
      _ ≤ _ := Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
  have h2 := hcost j
  unfold Scheme.verifyCost at h2
  unfold targetSet
  rw [Finset.card_erase_of_mem hroot]
  omega

lemma card_obs_le (S : Scheme paperParams) (i : Fin paperParams.numSets) :
    Fintype.card ((v : S.sets i) → BitVec (S.graph.len v)) ≤ 2 ^ 5248 := by
  rw [Fintype.card_pi]
  have : ∀ v : S.sets i, Fintype.card (BitVec (S.graph.len v)) = 2 ^ (S.graph.len v) := by
    intro v; convert Fintype.card_bitVec (S.graph.len v)
  simp only [this, Finset.prod_pow_eq_pow_sum]
  refine Nat.pow_le_pow_right (by norm_num) ?_
  have h := S.reveal_le i
  unfold Graph.revealBits at h
  rw [Finset.sum_coe_sort (S.sets i) S.graph.len]
  exact h

lemma h_zero_aux (S : Scheme paperParams) (ξ : S.graph.Rec) (i : Fin paperParams.numSets) :
    ∀ g ∈ targetSet S i, weight S i (obsCands S i ξ) g = 0 := by
  intro g hg
  have : g ∈ evalHashAt S i := Finset.mem_of_mem_erase hg
  simp [weight, this]

lemma ratio_le_countingFactor (ℓ : ℕ) (d : ℝ) (hd : 0 < d) (hd' : d ≤ 123) :
    (ℓ : ℝ) / countingFactor 22 5257 d ≤
      (ℓ : ℝ) / 100 * (123 / d) ^ 22 * (2 : ℝ) ^ 115 := by
  have hanti := Numerics.countingFactor_div_pow_strictAntiOn.antitoneOn
    (show d ∈ Set.Ioi (0:ℝ) from hd) (show (123:ℝ) ∈ Set.Ioi (0:ℝ) by norm_num) hd'
  have h100 := Numerics.hundred_lt_countingFactor
  have hdp : (0:ℝ) < d ^ 22 := by positivity
  have hcp : (0:ℝ) < (123:ℝ) ^ 22 := by positivity
  set β := countingFactor 22 5257 d
  set β' := countingFactor 22 5257 123
  have hβ' : 0 < β' := by
    have : (0:ℝ) < (2:ℝ) ^ 115 * β' := by linarith
    exact pos_of_mul_pos_right this (by positivity)
  -- β ≥ β' * d^22 / 123^22
  have hβ : β' * d ^ 22 / 123 ^ 22 ≤ β := by
    rw [div_le_div_iff₀ hcp hdp] at hanti
    rw [div_le_iff₀ hcp]
    nlinarith
  have hβpos : 0 < β := lt_of_lt_of_le (by positivity) hβ
  have key : 100 * (d ^ 22 / 123 ^ 22) ≤ (2:ℝ) ^ 115 * β := by
    calc 100 * (d ^ 22 / 123 ^ 22) ≤ (2 ^ 115 * β') * (d ^ 22 / 123 ^ 22) := by
          gcongr
      _ = 2 ^ 115 * (β' * d ^ 22 / 123 ^ 22) := by ring
      _ ≤ 2 ^ 115 * β := by gcongr
  have hℓ0 : (0:ℝ) ≤ ℓ := Nat.cast_nonneg ℓ
  have e : (ℓ : ℝ) / 100 * (123 / d) ^ 22 * (2 : ℝ) ^ 115 =
      (ℓ : ℝ) / (100 * (d ^ 22 / 123 ^ 22)) * (2 : ℝ) ^ 115 := by
    field_simp
  rw [e, div_mul_eq_mul_div, le_div_iff₀ (by positivity), div_mul_eq_mul_div,
    div_le_iff₀ hβpos]
  nlinarith

lemma card_filter_prod_eq {α β : Type*} [Fintype α] [Fintype β] (Q : α → β → Prop) :
    (Finset.univ.filter fun p : α × β => Q p.1 p.2).card =
      ∑ b, (Finset.univ.filter fun a => Q a b).card := by
  rw [Finset.card_filter, ← Finset.univ_product_univ, Finset.sum_product_right]
  simp only [Finset.card_filter]

lemma sum_card_filter_comm {α β : Type*} [Fintype α] [Fintype β] (Q : α → β → Prop) :
    ∑ b, (Finset.univ.filter fun a => Q a b).card =
      ∑ a, (Finset.univ.filter fun b => Q a b).card := by
  simp only [Finset.card_filter]
  exact Finset.sum_comm

lemma card_bad_le (S : Scheme paperParams) (hcost : ∀ i, S.verifyCost i ≤ 24) (ℓ : ℕ)
    (hℓ : ℓ < 100) (d : ℝ) (hd : 0 < d) (ξ : S.graph.Rec) :
    ((Finset.univ.filter fun i => ¬ D S i ℓ ξ < d).card : ℝ) ≤
      ((Finset.univ.filter fun i : Fin paperParams.numSets =>
          ((5248 : ℕ) : ℝ) + 9 < ∑ g, infoWeight (evalHashAt S i) (reveal S i) ξ g).card : ℝ) +
        (ℓ : ℝ) / countingFactor 22 5257 d := by
  have hℓM : ℓ < paperParams.numSets := lt_of_lt_of_le hℓ (by norm_num [paperParams])
  have hsub : (Finset.univ.filter fun i => ¬ D S i ℓ ξ < d) ⊆
      (Finset.univ.filter fun i : Fin paperParams.numSets =>
          ((5248 : ℕ) : ℝ) + 9 < ∑ g, infoWeight (evalHashAt S i) (reveal S i) ξ g) ∪
      (Finset.univ.filter fun i =>
        ∑ g, weight S i (obsCands S i ξ) g ≤ 5257 ∧
          (Finset.univ.filter fun j =>
            ∑ g ∈ targetSet S j, weight S i (obsCands S i ξ) g < d).card < ℓ + 1) := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt, Finset.mem_union] at hi ⊢
    by_cases h : ((5248 : ℕ) : ℝ) + 9 < ∑ g, infoWeight (evalHashAt S i) (reveal S i) ξ g
    · exact Or.inl h
    · right
      refine ⟨?_, ?_⟩
      · simp only [weight_eq_infoWeight]
        push_cast at h
        linarith
      · have := card_targetWeight_lt_le S i (obsCands S i ξ) hℓM hi
        exact Nat.lt_succ_of_le this
  have hB := card_few_low_weight_targets_le (ι := Fin paperParams.numSets) (targetSet S) 22
    (by norm_num) (card_targetSet_le S hcost) (fun i g => weight S i (obsCands S i ξ) g)
    (fun i g => weight_nonneg S i _ g) (fun i => h_zero_aux S ξ i) 5257 d (by norm_num) hd
    (ℓ + 1) (by omega)
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_union_le
    (Finset.univ.filter fun i : Fin paperParams.numSets =>
          ((5248 : ℕ) : ℝ) + 9 < ∑ g, infoWeight (evalHashAt S i) (reveal S i) ξ g)
    (Finset.univ.filter fun i =>
        ∑ g, weight S i (obsCands S i ξ) g ≤ 5257 ∧
          (Finset.univ.filter fun j =>
            ∑ g ∈ targetSet S j, weight S i (obsCands S i ξ) g < d).card < ℓ + 1)
  have h3 : ((Finset.univ.filter fun i => ¬ D S i ℓ ξ < d).card : ℝ) ≤ _ :=
    Nat.cast_le.mpr (h1.trans h2)
  rw [Nat.cast_add] at h3
  rw [Nat.cast_add, Nat.cast_one, add_sub_cancel_right] at hB
  refine h3.trans ?_
  have := add_le_add (le_refl
    ((Finset.univ.filter fun i : Fin paperParams.numSets =>
          ((5248 : ℕ) : ℝ) + 9 < ∑ g, infoWeight (evalHashAt S i) (reveal S i) ξ g).card : ℝ)) hB
  convert this using 3

lemma card_info_le (S : Scheme paperParams) (i : Fin paperParams.numSets) :
    ((Finset.univ.filter fun ξ : S.graph.Rec =>
          ((5248 : ℕ) : ℝ) + 9 < ∑ g, infoWeight (evalHashAt S i) (reveal S i) ξ g).card : ℝ) ≤
      (Fintype.card S.graph.Rec : ℝ) / 512 := by
  have h := card_infoWeight_gt_le (Z := S.graph.Assignment) (Out := BitVec 256)
    (n := S.graph.size) (evalHashAt S i) (reveal S i) 5248 (card_obs_le S i) 9 (by norm_num)
  have hR : (0:ℝ) < Fintype.card S.graph.Rec := by exact_mod_cast Fintype.card_pos
  have e : (2:ℝ) ^ (-(9:ℝ)) = 1 / 512 := by
    rw [Real.rpow_neg (by norm_num)]; norm_num
  rw [e] at h
  have e2 : (Fintype.card (S.graph.Assignment × (Fin S.graph.size → BitVec 256)) : ℝ) =
      Fintype.card S.graph.Rec := by
    exact_mod_cast Fintype.card_congr (Equiv.refl _)
  rw [e2, div_le_iff₀ hR] at h
  rw [le_div_iff₀ (by norm_num)]
  have h' := mul_le_mul_of_nonneg_right h (by norm_num : (0:ℝ) ≤ 512)
  convert h' using 1
  · congr 2
  · ring

theorem tail_bound (S : Scheme paperParams) (hcost : ∀ i, S.verifyCost i ≤ 24) (ℓ : ℕ)
    (hℓ : ℓ < 100) (d : ℝ) (hd : 0 < d) (hd' : d ≤ 123) :
    511 / 512 - (ℓ : ℝ) / 100 * (123 / d) ^ 22 ≤
      ((Finset.univ.filter fun p : Fin paperParams.numSets × S.graph.Rec =>
          D S p.1 ℓ p.2 < d).card : ℝ) /
        ((paperParams.numSets : ℝ) * (Fintype.card S.graph.Rec : ℝ)) := by
  have hM : (paperParams.numSets : ℝ) = 2 ^ 115 := by norm_num [paperParams]
  have hRpos : (0:ℝ) < Fintype.card S.graph.Rec := by exact_mod_cast Fintype.card_pos
  have htot : (Finset.univ.filter fun p : Fin paperParams.numSets × S.graph.Rec =>
          D S p.1 ℓ p.2 < d).card +
      (Finset.univ.filter fun p : Fin paperParams.numSets × S.graph.Rec =>
          ¬ D S p.1 ℓ p.2 < d).card = paperParams.numSets * Fintype.card S.graph.Rec := by
    rw [Finset.card_filter_add_card_filter_not]
    simp [Finset.card_univ]
  have hbadN : (Finset.univ.filter fun p : Fin paperParams.numSets × S.graph.Rec =>
          ¬ D S p.1 ℓ p.2 < d).card =
      ∑ ξ : S.graph.Rec, (Finset.univ.filter fun i => ¬ D S i ℓ ξ < d).card := by
    convert card_filter_prod_eq (fun (i : Fin paperParams.numSets) (ξ : S.graph.Rec) =>
      ¬ D S i ℓ ξ < d)
  have hinfo : ∑ ξ : S.graph.Rec, ((Finset.univ.filter fun i : Fin paperParams.numSets =>
          ((5248 : ℕ) : ℝ) + 9 < ∑ g, infoWeight (evalHashAt S i) (reveal S i) ξ g).card : ℝ) ≤
      (paperParams.numSets : ℝ) * ((Fintype.card S.graph.Rec : ℝ) / 512) := by
    have hc : ∑ ξ : S.graph.Rec, (Finset.univ.filter fun i : Fin paperParams.numSets =>
          ((5248 : ℕ) : ℝ) + 9 < ∑ g, infoWeight (evalHashAt S i) (reveal S i) ξ g).card =
        ∑ i : Fin paperParams.numSets, (Finset.univ.filter fun ξ : S.graph.Rec =>
          ((5248 : ℕ) : ℝ) + 9 < ∑ g, infoWeight (evalHashAt S i) (reveal S i) ξ g).card := by
      convert sum_card_filter_comm (fun (i : Fin paperParams.numSets) (ξ : S.graph.Rec) =>
        ((5248 : ℕ) : ℝ) + 9 < ∑ g, infoWeight (evalHashAt S i) (reveal S i) ξ g)
    rw [← Nat.cast_sum, hc, Nat.cast_sum]
    calc _ ≤ ∑ _i : Fin paperParams.numSets, (Fintype.card S.graph.Rec : ℝ) / 512 :=
          Finset.sum_le_sum fun i _ => card_info_le S i
      _ = _ := by simp [Finset.card_univ]
  have hbad : ((Finset.univ.filter fun p : Fin paperParams.numSets × S.graph.Rec =>
          ¬ D S p.1 ℓ p.2 < d).card : ℝ) ≤
      (paperParams.numSets : ℝ) * ((Fintype.card S.graph.Rec : ℝ) / 512) +
        (Fintype.card S.graph.Rec : ℝ) * ((ℓ : ℝ) / countingFactor 22 5257 d) := by
    rw [hbadN, Nat.cast_sum]
    calc _ ≤ ∑ ξ : S.graph.Rec,
          (((Finset.univ.filter fun i : Fin paperParams.numSets =>
            ((5248 : ℕ) : ℝ) + 9 < ∑ g, infoWeight (evalHashAt S i) (reveal S i) ξ g).card : ℝ) +
            (ℓ : ℝ) / countingFactor 22 5257 d) :=
          Finset.sum_le_sum fun ξ _ => card_bad_le S hcost ℓ hℓ d hd ξ
      _ = (∑ ξ : S.graph.Rec,
          ((Finset.univ.filter fun i : Fin paperParams.numSets =>
            ((5248 : ℕ) : ℝ) + 9 < ∑ g, infoWeight (evalHashAt S i) (reveal S i) ξ g).card : ℝ)) +
            (Fintype.card S.graph.Rec : ℝ) * ((ℓ : ℝ) / countingFactor 22 5257 d) := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ _ := by linarith [hinfo]
  have hnum := mul_le_mul_of_nonneg_left (ratio_le_countingFactor ℓ d hd hd') hRpos.le
  have hcast : ((Finset.univ.filter fun p : Fin paperParams.numSets × S.graph.Rec =>
          D S p.1 ℓ p.2 < d).card : ℝ) +
      ((Finset.univ.filter fun p : Fin paperParams.numSets × S.graph.Rec =>
          ¬ D S p.1 ℓ p.2 < d).card : ℝ) =
        (paperParams.numSets : ℝ) * Fintype.card S.graph.Rec := by
    exact_mod_cast htot
  rw [hM]
  rw [hM] at hcast hbad
  have hK : (0:ℝ) < (2:ℝ) ^ 115 := by positivity
  generalize (2:ℝ) ^ 115 = K at hK hcast hbad hnum ⊢
  rw [le_div_iff₀ (mul_pos hK hRpos)]
  linarith

end Analysis

end OptimalOTS
