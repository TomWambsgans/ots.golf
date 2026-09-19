import Submissions.RiscvUpper.ForestVerifierProof

/-! The sequential disclosure cursor stays within the transmitted payload. -/

noncomputable section
open scoped Classical

namespace OptimalOTS.RiscvUpperForest.ForestVerifier

open Forest Forest.Name

set_option allowUnsafeReducibility true
attribute [local reducible] Forest.graph
attribute [local irreducible] Forest.setsName Forest.fixedPositions Forest.fixedDigits

theorem consumedBits_word (i : Idx paperParams) (n : Name) :
    consumedBits i n = if disclosed (fixedPositions i) n then 128 else 0 := by
  unfold consumedBits
  split_ifs with hd
  · exact (fixedCut_isCut i).values n (by simpa only [setsName] using (disclosed_eq i n).mp hd)
  · rfl

theorem consumedBits_aligned (i : Idx paperParams) (n : Name) : consumedBits i n % 128 = 0 := by
  rw [consumedBits_word]
  split <;> decide

/-- Exactly 41 whole words are consumed over the complete node sequence. -/
theorem total_consumed (i : Idx paperParams) : (order.map (consumedBits i)).sum = 5248 := by
  let cost (v : Fin N) := if v ∈ fins (setsName i) then graph.len v else 0
  have pointwise (n : Name) : consumedBits i n = cost n.fin := by
    simp only [cost, consumedBits, mem_fins, ← disclosed_eq, lenF_fin]
  have lists : order.map (consumedBits i) = (List.finRange N).map cost := by
    rw [← order_fin, List.map_map]
    apply List.map_congr_left
    intro n _
    exact pointwise n
  rw [lists, ← List.sum_toFinset cost (List.nodup_finRange N), List.toFinset_finRange]
  change (∑ v : Fin N, if v ∈ fins (setsName i) then graph.len v else 0) = 5248
  rw [← Finset.sum_filter]
  have total := fixed_revealBits i
  change (∑ v ∈ fins (setsName i), graph.len v) = 5248 at total
  simpa only [Finset.filter_mem_eq_inter, Finset.univ_inter] using total

end OptimalOTS.RiscvUpperForest.ForestVerifier
