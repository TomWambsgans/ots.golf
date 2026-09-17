import OptimalOTS.Statement

/-! Every disclosure set excludes the root, which is a hash node of cost at least one. -/

namespace OptimalOTS

open scoped Classical

theorem Graph.one_le_nodeCost_of_isHash {P : Params} (G : Graph P) (v : Fin G.size)
    (hv : (G.kind v).IsHash) : 1 ≤ G.nodeCost v := by
  unfold Graph.nodeCost
  cases h : G.kind v with
  | source => simp [h, NodeKind.IsHash] at hv
  | det ps hp f hf => simp [h, NodeKind.IsHash] at hv
  | hash p hp hl => exact le_max_left _ _

theorem Scheme.one_le_reconstructCost {P : Params} (S : Scheme P) (i : Fin P.numSets) :
    1 ≤ S.graph.reconstructCost (S.sets i) := by
  have hr : S.graph.root ∈ S.graph.evaluated (S.sets i) := by
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, Graph.Visited.root, S.root_not_mem i⟩
  exact (S.graph.one_le_nodeCost_of_isHash _ S.graph.root_isHash).trans
    (Finset.single_le_sum (fun v _ => Nat.zero_le (S.graph.nodeCost v)) hr)

/-- This bound holds for every scheme, independently of security or the numerical parameters. -/
theorem Scheme.two_le_verifyCost {P : Params} (S : Scheme P) (i : Fin P.numSets) :
    2 ≤ S.verifyCost i := by
  have hi : 1 ≤ idxCost P := le_max_left _ _
  have hr := S.one_le_reconstructCost i
  unfold Scheme.verifyCost
  omega

end OptimalOTS
