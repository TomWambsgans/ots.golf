import Submissions.RiscvUpper.FixedChoice

/-!
# The fixed-layout forest

A computably indexed family of cuts with 41 revealed 128-bit values. Verification
costs 141 compressions. The graph and security argument are shared with the original forest.
-/

open OracleSpec OracleComp ENNReal

noncomputable section

open scoped Classical

namespace OptimalOTS

namespace Forest

open Name

/-- A fixed disclosure layout, with chain positions decoded from the index. -/
def setsName (i : Fin (2 ^ 115)) : Finset Name := cutOf (fixedChoice i)

theorem setsName_injective : Function.Injective setsName := fixedCut_injective

theorem numSets_eq : paperParams.numSets = 2 ^ 115 := rfl

/-- The concrete scheme. -/
def forestScheme : Scheme paperParams where
  graph := graph
  sets := fun i => fins (setsName i)
  root_not_mem := by
    intro i
    show rh.fin ∉ fins (setsName i)
    rw [mem_fins]
    exact (fixedCut_isCut i).rh_not_mem
  no_hidden_source := by
    intro i
    exact (no_hidden_source_iff (setsName i)).mpr (fixedCut_isCut i).covers
  reveal_le := by
    intro i
    show graph.revealBits (fins (setsName i)) ≤ 5248
    rw [revealBits_eq]
    change ∑ n ∈ cutOf (fixedChoice i), n.len ≤ 5248
    rw [Finset.sum_const_nat fun n hn => (fixedCut_isCut i).values n hn]
    have := fixedCut_card i
    omega
  keygen_le := by
    show graph.keygenCost ≤ 1024
    rw [graph_keygenCost]
    norm_num

theorem forestScheme_graph : forestScheme.graph = graph := rfl

theorem forestScheme_sets (i : Fin paperParams.numSets) : forestScheme.sets i = fins (setsName i) :=
  rfl

theorem forestScheme_sets_injective : Function.Injective forestScheme.sets := by
  intro i j h
  apply setsName_injective
  have := congrArg names h
  simpa only [forestScheme_sets, names_fins] using this

theorem isCut_setsName (i : Fin (2 ^ 115)) : IsCut (setsName i) :=
  fixedCut_isCut i

theorem cost_setsName (i : Fin (2 ^ 115)) : ∑ n ∈ evaluatedSet (setsName i), n.cost = 140 :=
  fixedCut_cost i

/-- Every signature verifies in `141` compressions. -/
theorem forestScheme_verifyCost (i : Fin paperParams.numSets) : forestScheme.verifyCost i = 141 := by
  show idxCost paperParams + graph.reconstructCost (fins (setsName i)) = 141
  have hidx : idxCost paperParams = 1 := by decide
  rw [reconstructCost_eq, hidx]
  have h := cost_setsName i
  omega

end Forest

end OptimalOTS
