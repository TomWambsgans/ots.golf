import Submissions.RiscvUpper.FixedChoice
import Submissions.RiscvUpper.GScheme

/-!
# The nibble-layout forest

A family of cuts indexed by the accepted indices, with 41 revealed 128-bit values. Verification
costs 186 compressions. The graph and security argument are shared with the original forest.
-/

open OracleSpec OracleComp ENNReal

noncomputable section

open scoped Classical

namespace OptimalOTS

namespace Forest

open Name

/-- A fixed disclosure layout, with chain positions decoded from the index. -/
def setsName (i : Idx paperParams) : Finset Name := cutOf (fixedChoice i)

theorem setsName_injective : Function.Injective setsName := fixedCut_injective

/-- The concrete scheme. -/
def forestScheme : GScheme paperParams where
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

theorem isCut_setsName (i : Idx paperParams) : IsCut (setsName i) :=
  fixedCut_isCut i

theorem cost_setsName (i : Idx paperParams) : ∑ n ∈ evaluatedSet (setsName i), n.cost = 185 :=
  fixedCut_cost i

/-- Every signature verifies in `186` compressions. -/
theorem forestScheme_verifyCost (i : Idx paperParams) : forestScheme.verifyCost i = 186 := by
  show idxCost paperParams + graph.reconstructCost (fins (setsName i)) = 186
  have hidx : idxCost paperParams = 1 := by decide
  rw [reconstructCost_eq, hidx]
  have h := cost_setsName i
  omega

end Forest

end OptimalOTS
