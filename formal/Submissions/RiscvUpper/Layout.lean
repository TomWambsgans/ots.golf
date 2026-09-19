import Submissions.RiscvUpper.Wire
import Submissions.RiscvUpper.Program

/-! Exact signature layout and table bounds used by the assembly refinement. -/

noncomputable section
open scoped Classical

namespace OptimalOTS.Forest

theorem chainNode_injective (positions : Fin 63 → Fin 15) :
    Function.Injective (fun k => chainNode k (positions k)) := by
  intro k l equal
  unfold chainNode at equal
  dsimp only at equal
  split_ifs at equal <;> simp only [Name.src.injEq, Name.cv.injEq, reduceCtorEq] at equal
  · exact equal
  · exact equal.1

theorem fixedCut_card_eq (i : Idx paperParams) : (cutOf (fixedChoice i)).card = 41 := by
  have disjointEG : Disjoint (fixedE.image Name.ev) (fixedG.image Name.gv) := by
    apply Finset.disjoint_left.mpr
    intro n hn hm
    obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp hn
    obtain ⟨g, _, equal⟩ := Finset.mem_image.mp hm
    cases equal
  have disjointChains : Disjoint (fixedE.image Name.ev ∪ fixedG.image Name.gv)
      ((active fixedE fixedG).image fun k => chainNode k (fixedPositions i k)) := by
    apply Finset.disjoint_left.mpr
    intro n hn hm
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hm
    rcases Finset.mem_union.mp hn with he | hg
    · obtain ⟨e, _, equal⟩ := Finset.mem_image.mp he
      exact chainNode_ne_ev k _ e equal.symm
    · obtain ⟨g, _, equal⟩ := Finset.mem_image.mp hg
      exact chainNode_ne_gv k _ g equal.symm
  change (fixedE.image Name.ev ∪ fixedG.image Name.gv ∪
    (active fixedE fixedG).image (fun k => chainNode k (fixedPositions i k))).card = 41
  rw [Finset.card_union_of_disjoint disjointChains,
    Finset.card_union_of_disjoint disjointEG,
    Finset.card_image_of_injective _ (fun _ _ h => Name.ev.inj h),
    Finset.card_image_of_injective _ (fun _ _ h => Name.gv.inj h),
    Finset.card_image_of_injective _ (chainNode_injective _),
    card_active fixedE fixedG fixedG_allowed, fixedE_card, fixedG_card]

theorem fixed_revealBits (i : Idx paperParams) :
    forestScheme.graph.revealBits (forestScheme.sets i) = 5248 := by
  change graph.revealBits (fins (cutOf (fixedChoice i))) = 5248
  rw [revealBits_eq, Finset.sum_const_nat (fun n hn => (fixedCut_isCut i).values n hn),
    fixedCut_card_eq]

end OptimalOTS.Forest

namespace OptimalOTS.RiscvUpperForest.Wire

/-- The machine's fixed-length check is exactly the specification's payload-length check. -/
theorem payload_length_iff (bits : List Bool) (i : Idx paperParams) :
    (decode bits).2.length = Forest.forestScheme.graph.revealBits (Forest.forestScheme.sets i) ↔
      bits.length = 5504 := by
  rw [Forest.fixed_revealBits]
  simp only [decode, List.length_drop]
  omega

end OptimalOTS.RiscvUpperForest.Wire
