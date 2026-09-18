import Submissions.RiscvUpper.Cuts
import Submissions.RiscvUpper.Unrank

/-!
# A computable family for the first machine implementation

Reveal subtree digests 5 and 6, group digests 12, 13 and 14, and one value from each
of chains 0 through 35. The remaining chain lengths sum to 121. There are at least
`2^115` such tuples, decoded in lexicographic order by `unrankComposition`.
-/

namespace OptimalOTS.Forest

theorem comp_36_121 : comp 36 121 = 41695891754464226932279920354981492 := by
  rw [← compTable_getD 121 36 121 le_rfl]
  decide +kernel

theorem fixed_count : 2 ^ 115 ≤ comp 36 121 := by rw [comp_36_121]; norm_num

def fixedE : Finset (Fin 7) := {5, 6}
def fixedG : Finset (Fin 21) := {12, 13, 14}

theorem fixedE_card : fixedE.card = 2 := by decide
theorem fixedG_card : fixedG.card = 3 := by decide
theorem fixedG_allowed : fixedG ⊆ allowed fixedE := by decide

theorem fixed_active (k : Fin 63) : k ∈ active fixedE fixedG ↔ k.val < 36 := by
  simp only [active, fixedE, fixedG, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_insert, Finset.mem_singleton, subtreeOfChain, groupOfChain, Fin.ext_iff]
  omega

def fixedDigits (i : Fin (2 ^ 115)) (k : Fin 36) : Fin 15 :=
  let values := unrankComposition 36 121 i
  have hs := unrankComposition_spec 36 121 i (i.isLt.trans_le fixed_count)
  have hk : k.val < values.length := by rw [hs.1]; exact k.isLt
  ⟨values[k.val], hs.2.1 _ (List.getElem_mem hk)⟩

theorem fixedDigits_values (i : Fin (2 ^ 115)) :
    List.ofFn (fun k => (fixedDigits i k).val) = unrankComposition 36 121 i := by
  have hs := unrankComposition_spec 36 121 i (i.isLt.trans_le fixed_count)
  apply List.ext_get (by simp [hs.1])
  intro n h₁ h₂
  simp only [List.get_eq_getElem, List.getElem_ofFn, fixedDigits]

theorem fixedDigits_sum (i : Fin (2 ^ 115)) : ∑ k, (fixedDigits i k).val = 121 := by
  rw [← List.sum_ofFn, fixedDigits_values]
  exact (unrankComposition_spec 36 121 i (i.isLt.trans_le fixed_count)).2.2.1

theorem fixedDigits_injective : Function.Injective fixedDigits := by
  intro i j h
  have hv : unrankComposition 36 121 i = unrankComposition 36 121 j := by
    rw [← fixedDigits_values i, ← fixedDigits_values j, h]
  have hr := congrArg (rankComposition 121) hv
  rw [(unrankComposition_spec 36 121 i (i.isLt.trans_le fixed_count)).2.2.2,
    (unrankComposition_spec 36 121 j (j.isLt.trans_le fixed_count)).2.2.2] at hr
  exact Fin.ext hr

def fixedPositions (i : Fin (2 ^ 115)) (k : Fin 63) : Fin 15 :=
  if hk : k.val < 36 then Fin.rev (fixedDigits i ⟨k.val, hk⟩) else 14

def fixedChoice (i : Fin (2 ^ 115)) : Choice := (fixedE, fixedG, fixedPositions i)

theorem fixedPositions_normal (i : Fin (2 ^ 115)) :
    ∀ k ∉ active fixedE fixedG, fixedPositions i k = 14 := by
  intro k hk
  simp only [fixedPositions, dif_neg (mt (fixed_active k).mpr hk)]

theorem fixedPositions_sum (i : Fin (2 ^ 115)) :
    ∑ k ∈ active fixedE fixedG, (14 - (fixedPositions i k).val) = 121 := by
  rw [← fixedDigits_sum i]
  apply Finset.sum_bij (fun k hk => (⟨k.val, (fixed_active k).mp hk⟩ : Fin 36))
  · intro k hk; exact Finset.mem_univ _
  · intro k hk l hl h; exact Fin.ext (congrArg (fun v : Fin 36 => v.val) h)
  · intro k _
    refine ⟨⟨k.val, by omega⟩, (fixed_active _).mpr k.isLt, rfl⟩
  · intro k hk
    simp only [fixedPositions, dif_pos ((fixed_active k).mp hk), Fin.val_rev]
    have := (fixedDigits i ⟨k.val, (fixed_active k).mp hk⟩).isLt
    omega

theorem fixedPositions_mem (i : Fin (2 ^ 115)) :
    fixedPositions i ∈ positions (active fixedE fixedG) 121 :=
  (mem_positions _ _ _).mpr ⟨fixedPositions_normal i, fixedPositions_sum i⟩

attribute [local irreducible] fixedDigits unrankComposition

theorem fixedCut_injective : Function.Injective (fun i => cutOf (fixedChoice i)) := by
  intro i j h
  have hc := cutOf_injective_of_normal (c := fixedChoice i) (c' := fixedChoice j)
    (fixedPositions_normal i) (fixedPositions_normal j) h
  apply fixedDigits_injective
  funext k
  have hp := congrFun (congrArg (fun c : Choice => c.2.2) hc) ⟨k.val, by omega⟩
  simpa [fixedChoice, fixedPositions, k.isLt] using hp

theorem fixedCut_isCut (i : Fin (2 ^ 115)) : IsCut (cutOf (fixedChoice i)) :=
  isCut_cutOf_of_subset fixedG_allowed

theorem fixedCut_card (i : Fin (2 ^ 115)) : (cutOf (fixedChoice i)).card ≤ 41 := by
  have h1 := Finset.card_union_le (fixedE.image Name.ev ∪ fixedG.image Name.gv)
    ((active fixedE fixedG).image fun k => chainNode k (fixedPositions i k))
  have h2 := Finset.card_union_le (fixedE.image Name.ev) (fixedG.image Name.gv)
  have h3 : (fixedE.image Name.ev).card ≤ fixedE.card := Finset.card_image_le
  have h4 : (fixedG.image Name.gv).card ≤ fixedG.card := Finset.card_image_le
  have h5 : ((active fixedE fixedG).image fun k => chainNode k (fixedPositions i k)).card ≤
      (active fixedE fixedG).card := Finset.card_image_le
  rw [card_active fixedE fixedG fixedG_allowed, fixedE_card, fixedG_card] at h5
  rw [fixedE_card] at h3
  rw [fixedG_card] at h4
  change (fixedE.image Name.ev ∪ fixedG.image Name.gv ∪
    (active fixedE fixedG).image (fun k => chainNode k (fixedPositions i k))).card ≤ 41
  omega

theorem fixedCut_cost (i : Fin (2 ^ 115)) :
    ∑ n ∈ evaluatedSet (cutOf (fixedChoice i)), n.cost = 140 := by
  rw [cost_cutOf_of_positions fixedG_allowed (fixedPositions_mem i)]
  change 121 + (21 - 3 * fixedE.card - fixedG.card) + (7 - fixedE.card) + 2 = 140
  rw [fixedE_card, fixedG_card]

end OptimalOTS.Forest
