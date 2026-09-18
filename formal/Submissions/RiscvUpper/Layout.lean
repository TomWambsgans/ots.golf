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

theorem fixedCut_card_eq (i : Fin (2 ^ 115)) : (cutOf (fixedChoice i)).card = 41 := by
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

theorem fixed_revealBits (i : Fin paperParams.numSets) :
    forestScheme.graph.revealBits (forestScheme.sets i) = 5248 := by
  change Fin (2 ^ 115) at i
  change graph.revealBits (fins (cutOf (fixedChoice i))) = 5248
  rw [revealBits_eq, Finset.sum_const_nat (fun n hn => (fixedCut_isCut i).values n hn),
    fixedCut_card_eq]

end OptimalOTS.Forest

namespace OptimalOTS.RiscvUpperForest.Wire

/-- The machine's fixed-length check is exactly the specification's payload-length check. -/
theorem payload_length_iff (bits : List Bool) (i : Fin paperParams.numSets) :
    (decode bits).2.length = Forest.forestScheme.graph.revealBits (Forest.forestScheme.sets i) ↔
      bits.length = 5504 := by
  rw [Forest.fixed_revealBits]
  simp only [decode, List.length_drop]
  omega

end OptimalOTS.RiscvUpperForest.Wire

namespace OptimalOTS.RiscvUpperProgram

set_option maxRecDepth 100000 in
theorem table_counts_fit_checked :
    ((List.range 36).flatMap (Forest.compositionTable 121)).all (fun n => decide (n < 2 ^ 128)) =
      true := by decide +kernel

/-- Both 64-bit loads together recover a complete table entry without truncation. -/
theorem table_counts_fit (n s : ℕ) (hn : n < 36) (hs : s ≤ 121) :
    Forest.comp n s < 2 ^ 128 := by
  have member : Forest.comp n s ∈
      (List.range 36).flatMap (Forest.compositionTable 121) := by
    apply List.mem_flatMap.mpr
    refine ⟨n, List.mem_range.mpr hn, ?_⟩
    rw [← Forest.compositionTable_get 121 n s hs]
    have length : (Forest.compositionTable 121 n).length = 122 := by
      cases n <;> simp [Forest.compositionTable]
    have index : s < (Forest.compositionTable 121 n).length := by omega
    simpa only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem index,
      Option.getD_some] using (List.getElem_mem index)
  exact of_decide_eq_true (List.all_eq_true.mp table_counts_fit_checked _ member)

end OptimalOTS.RiscvUpperProgram
