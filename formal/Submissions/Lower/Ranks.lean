import Submissions.Lower.AnalysisDefs
import Submissions.Lower.EntropyLemmas

/-!
# Weights and ranks

Weights are nonnegative, ranks enumerate the indices bijectively, the observed index has rank
zero, and few targets are lighter than the target of a given rank.
-/

open OracleSpec OracleComp ENNReal

noncomputable section

open scoped Classical

namespace OptimalOTS

namespace Analysis

open Attack

variable {P : Params} (S : Scheme P)

theorem weight_nonneg (i : Fin P.numSets) (C : Finset S.graph.Rec) (g : Fin S.graph.size) :
    0 ≤ weight S i C g := by
  unfold weight
  split_ifs
  · exact le_rfl
  · exact sub_nonneg.mpr (condEntropy_le_logb_card _ _ _)

theorem targetWeight_nonneg (i : Fin P.numSets) (C : Finset S.graph.Rec) (j : Fin P.numSets) :
    0 ≤ targetWeight S i C j :=
  Finset.sum_nonneg fun g _ => weight_nonneg S i C g

theorem key_injective (i : Fin P.numSets) (C : Finset S.graph.Rec) :
    Function.Injective (key S i C) := by
  intro j j' h
  simp only [key, toLex_inj, Prod.mk.injEq] at h
  exact Fin.ext h.2.2

theorem rank_lt_rank_of_key_lt (i : Fin P.numSets) (C : Finset S.graph.Rec)
    {j j' : Fin P.numSets} (h : key S i C j < key S i C j') : rank S i C j < rank S i C j' := by
  unfold rank
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · exact ⟨j, by simp [h], by simp⟩
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact hx.trans h

theorem rank_lt (i : Fin P.numSets) (C : Finset S.graph.Rec) (j : Fin P.numSets) :
    rank S i C j < P.numSets := by
  unfold rank
  calc _ < (Finset.univ : Finset (Fin P.numSets)).card := by
        apply Finset.card_lt_card
        rw [Finset.ssubset_iff_of_subset (Finset.subset_univ _)]
        exact ⟨j, Finset.mem_univ _, by simp⟩
    _ = P.numSets := by simp

theorem rank_injective (i : Fin P.numSets) (C : Finset S.graph.Rec) :
    Function.Injective (rank S i C) := by
  intro j j' h
  rcases lt_trichotomy (key S i C j) (key S i C j') with hl | he | hl
  · exact absurd h (rank_lt_rank_of_key_lt S i C hl).ne
  · exact key_injective S i C he
  · exact absurd h (rank_lt_rank_of_key_lt S i C hl).ne'

theorem rank_surj (i : Fin P.numSets) (C : Finset S.graph.Rec) {ℓ : ℕ}
    (hℓ : ℓ < P.numSets) : ∃ j, rank S i C j = ℓ := by
  have hsub : Finset.univ.image (rank S i C) ⊆ Finset.range P.numSets := by
    intro x hx
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx
    obtain ⟨j, rfl⟩ := hx
    exact Finset.mem_range.mpr (rank_lt S i C j)
  have hcard : (Finset.univ.image (rank S i C)).card = (Finset.range P.numSets).card := by
    rw [Finset.card_image_of_injective _ (rank_injective S i C)]
    simp
  have heq := Finset.eq_of_subset_of_card_le hsub hcard.ge
  have : ℓ ∈ Finset.univ.image (rank S i C) := heq ▸ Finset.mem_range.mpr hℓ
  simpa using this

theorem rank_rankElem (i : Fin P.numSets) (C : Finset S.graph.Rec) {ℓ : ℕ}
    (hℓ : ℓ < P.numSets) : rank S i C (rankElem S i C ℓ) = ℓ := by
  have h := rank_surj S i C hℓ
  unfold rankElem
  rw [dif_pos h]
  exact Classical.choose_spec h

theorem targetWeight_self (i : Fin P.numSets) (C : Finset S.graph.Rec) :
    targetWeight S i C i = 0 := by
  unfold targetWeight
  apply Finset.sum_eq_zero
  intro g hg
  have : g ∈ evalHashAt S i := Finset.mem_of_mem_erase hg
  simp [weight, this]

theorem rank_self (i : Fin P.numSets) (C : Finset S.graph.Rec) : rank S i C i = 0 := by
  unfold rank
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro j _ hj
  simp only [key, Prod.Lex.toLex_lt_toLex, targetWeight_self] at hj
  rcases hj with hj | ⟨hj1, hj2⟩
  · exact absurd hj (not_lt.mpr (targetWeight_nonneg S i C j))
  · split_ifs at hj2 with hji
    · subst hji; simp at hj2
    · simp at hj2

theorem rankElem_zero (i : Fin P.numSets) (C : Finset S.graph.Rec) :
    rankElem S i C 0 = i := by
  have h : ∃ j, rank S i C j = 0 := ⟨i, rank_self S i C⟩
  unfold rankElem
  rw [dif_pos h]
  exact rank_injective S i C ((Classical.choose_spec h).trans (rank_self S i C).symm)

/-- At most `ℓ` targets are lighter than `d` when the target of rank `ℓ` weighs at least `d`. -/
theorem card_targetWeight_lt_le (i : Fin P.numSets) (C : Finset S.graph.Rec) {ℓ : ℕ}
    (hℓ : ℓ < P.numSets) {d : ℝ} (hd : d ≤ targetWeight S i C (rankElem S i C ℓ)) :
    (Finset.univ.filter fun j => targetWeight S i C j < d).card ≤ ℓ := by
  rw [← rank_rankElem S i C hℓ]
  unfold rank
  apply Finset.card_le_card
  intro j hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
  simp only [key, Prod.Lex.toLex_lt_toLex]
  exact Or.inl (lt_of_lt_of_le hj hd)

theorem rkOf_existsUnique (i : Fin P.numSets) (C : Finset S.graph.Rec)
    (hM : P.numSets ≤ 2 ^ P.idxBits) {ℓ : ℕ} (hℓ : ℓ < 100) (hℓM : ℓ < P.numSets) :
    ∃! n, n < 2 ^ P.idxBits ∧ rkOf S i C n = some ℓ := by
  refine ⟨(rankElem S i C ℓ).val, ⟨lt_of_lt_of_le (rankElem S i C ℓ).isLt hM, ?_⟩, ?_⟩
  · unfold rkOf
    rw [dif_pos (rankElem S i C ℓ).isLt]
    simp only [Fin.eta, rank_rankElem S i C hℓM, if_pos hℓ]
  · rintro m ⟨_, hm⟩
    unfold rkOf at hm
    split_ifs at hm with h1 h2
    have hr : rank S i C ⟨m, h1⟩ = ℓ := Option.some.inj hm
    have := rank_injective S i C (hr.trans (rank_rankElem S i C hℓM).symm)
    exact congrArg Fin.val this

theorem rkOf_lt (i : Fin P.numSets) (C : Finset S.graph.Rec) {n ℓ : ℕ}
    (h : rkOf S i C n = some ℓ) : ℓ < 100 := by
  unfold rkOf at h
  split_ifs at h with h1 h2
  rw [← Option.some.inj h]
  exact h2

end Analysis

end OptimalOTS
