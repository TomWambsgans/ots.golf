import Submissions.Upper.Cuts

/-!
# The concrete scheme as a `Scheme paperParams`

`flatScheme` is the flat scheme: the graph of `Flat.Names` (41 chains of length 20 under the
root), with the `2 ^ 115` disclosure sets chosen injectively from the family of `Flat.Cuts`.
Every signature verifies in `109` compressions (`flatScheme_verifyCost`).
-/

open OracleSpec OracleComp ENNReal

noncomputable section

open scoped Classical

namespace OptimalOTS

namespace Flat

open Name

/-- The disclosure sets, indexed injectively by `Fin (2 ^ 115)`. -/
def setsName (i : Fin (2 ^ 115)) : Finset Name :=
  (family.equivFin.symm (Fin.castLE card_family i)).1

theorem setsName_mem (i : Fin (2 ^ 115)) : setsName i ∈ family :=
  (family.equivFin.symm (Fin.castLE card_family i)).2

theorem setsName_injective : Function.Injective setsName := by
  intro i j h
  unfold setsName at h
  exact Fin.castLE_injective _ (family.equivFin.symm.injective (Subtype.ext h))

theorem numSets_eq : paperParams.numSets = 2 ^ 115 := rfl

/-- The concrete scheme. -/
def flatScheme : Scheme paperParams where
  graph := graph
  sets := fun i => fins (setsName i)
  root_not_mem := by
    intro i
    show rh.fin ∉ fins (setsName i)
    rw [mem_fins]
    exact (isCut_of_mem_family (setsName_mem i)).rh_not_mem
  no_hidden_source := by
    intro i
    exact (no_hidden_source_iff (setsName i)).mpr (isCut_of_mem_family (setsName_mem i)).covers
  reveal_le := by
    intro i
    show graph.revealBits (fins (setsName i)) ≤ 5248
    rw [revealBits_eq, Finset.sum_const_nat fun n hn => (isCut_of_mem_family (setsName_mem i)).values n hn]
    have := card_le_of_mem_family (setsName_mem i)
    omega
  keygen_le := by
    show graph.keygenCost ≤ 1024
    rw [graph_keygenCost]
    norm_num

theorem flatScheme_graph : flatScheme.graph = graph := rfl

theorem flatScheme_sets (i : Fin paperParams.numSets) : flatScheme.sets i = fins (setsName i) :=
  rfl

theorem flatScheme_sets_injective : Function.Injective flatScheme.sets := by
  intro i j h
  apply setsName_injective
  have := congrArg names h
  simpa only [flatScheme_sets, names_fins] using this

theorem isCut_setsName (i : Fin (2 ^ 115)) : IsCut (setsName i) :=
  isCut_of_mem_family (setsName_mem i)

theorem cost_setsName (i : Fin (2 ^ 115)) : ∑ n ∈ evaluatedSet (setsName i), n.cost = 107 :=
  cost_of_mem_family (setsName_mem i)

/-- Every signature verifies in `109` compressions: two for the index query and `107` for reconstruction. -/
theorem flatScheme_verifyCost (i : Fin paperParams.numSets) : flatScheme.verifyCost i = 109 := by
  show idxCost paperParams + graph.reconstructCost (fins (setsName i)) = 109
  have hidx : idxCost paperParams = 2 := by decide
  rw [reconstructCost_eq, hidx]
  have h := cost_setsName i
  omega

end Flat

end OptimalOTS
