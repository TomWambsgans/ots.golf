import OptimalOTS.Disclosure
import Submissions.DisclosureUpper.Scheme

/-!
# The forest's disclosures represent at most 41 hash outputs

Each disclosed forest value is either a source, which contributes no hash origin, or the
128-bit truncation of one hash node. Taking the union over at most 41 disclosed values proves
membership in the partial-disclosure framework, including its looser limit of 46 origins.
-/

noncomputable section
open scoped Classical

namespace OptimalOTS.Forest

private theorem origin_at_hash {P : Params} {G : Graph P} {h v : Fin G.size}
    (hv : (G.kind v).IsHash) : G.HashOrigin h v ↔ h = v := by
  constructor
  · intro ho
    cases ho with
    | hash => rfl
    | step hn _ _ => exact False.elim (hn hv)
  · rintro rfl
    exact Graph.HashOrigin.hash hv

private theorem origins_hash {P : Params} {G : Graph P} {v : Fin G.size}
    (hv : (G.kind v).IsHash) : G.hashOrigins v = {v} := by
  ext h
  simp only [Graph.hashOrigins, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_singleton]
  exact origin_at_hash hv

private theorem origins_single_parent {P : Params} {G : Graph P} {v p : Fin G.size}
    (hv : ¬ (G.kind v).IsHash) (hp : (G.kind v).parents = {p}) :
    G.hashOrigins v = G.hashOrigins p := by
  ext h
  simp only [Graph.hashOrigins, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro ho
    cases ho with
    | hash hh => exact False.elim (hv hh)
    | step _ hw ho =>
      rw [hp, Finset.mem_singleton] at hw
      simpa [hw] using ho
  · intro ho
    exact Graph.HashOrigin.step hv (by rw [hp]; exact Finset.mem_singleton_self _) ho

private theorem origins_no_parents {P : Params} {G : Graph P} {v : Fin G.size}
    (hv : ¬ (G.kind v).IsHash) (hp : (G.kind v).parents = ∅) :
    G.hashOrigins v = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro h hh
  obtain ⟨_, ho⟩ := Finset.mem_filter.mp hh
  cases ho with
  | hash hh => exact hv hh
  | step _ hw _ => rw [hp] at hw; exact Finset.notMem_empty _ hw

theorem hashOrigins_src (k : Fin 63) : graph.hashOrigins (Name.src k).fin = ∅ := by
  apply origins_no_parents
  · simp [graph_isHash_fin, Name.cost]
  · rw [graph_parents_fin]; rfl

theorem hashOrigins_cv (k : Fin 63) (t : Fin 14) :
    graph.hashOrigins (Name.cv k t).fin = {(Name.ch k t).fin} := by
  exact (origins_single_parent (G := graph) (v := (Name.cv k t).fin)
    (p := (Name.ch k t).fin)
    (by simp [graph_isHash_fin, Name.cost])
    (by rw [graph_parents_fin]; rfl)).trans
    (origins_hash ((graph_isHash_fin _).mpr (by simp [Name.cost])))

theorem hashOrigins_gv (j : Fin 21) :
    graph.hashOrigins (Name.gv j).fin = {(Name.gh j).fin} := by
  exact (origins_single_parent (G := graph) (v := (Name.gv j).fin)
    (p := (Name.gh j).fin)
    (by simp [graph_isHash_fin, Name.cost])
    (by rw [graph_parents_fin]; rfl)).trans
    (origins_hash ((graph_isHash_fin _).mpr (by simp [Name.cost])))

theorem hashOrigins_ev (l : Fin 7) :
    graph.hashOrigins (Name.ev l).fin = {(Name.eh l).fin} := by
  exact (origins_single_parent (G := graph) (v := (Name.ev l).fin)
    (p := (Name.eh l).fin)
    (by simp [graph_isHash_fin, Name.cost])
    (by rw [graph_parents_fin]; rfl)).trans
    (origins_hash ((graph_isHash_fin _).mpr (by simp [Name.cost])))

theorem card_hashOrigins_value (n : Name) (hn : n.len = 128) :
    (graph.hashOrigins n.fin).card ≤ 1 := by
  cases n with
  | src k => rw [hashOrigins_src]; exact Nat.zero_le _
  | cv k t => rw [hashOrigins_cv]; exact (Finset.card_singleton _).le
  | gv j => rw [hashOrigins_gv]; exact (Finset.card_singleton _).le
  | ev l => rw [hashOrigins_ev]; exact (Finset.card_singleton _).le
  | _ => simp only [Name.len] at hn; omega

theorem card_disclosureOrigins_fins {A : Finset Name}
    (hA : ∀ n ∈ A, n.len = 128) :
    (graph.disclosureOrigins (fins A)).card ≤ A.card := by
  calc
    (graph.disclosureOrigins (fins A)).card
        ≤ ∑ v ∈ fins A, (graph.hashOrigins v).card := Finset.card_biUnion_le
    _ ≤ ∑ _v ∈ fins A, 1 := by
      apply Finset.sum_le_sum
      intro v hv
      rw [fins, Finset.mem_map] at hv
      obtain ⟨n, hn, rfl⟩ := hv
      exact card_hashOrigins_value n (hA n hn)
    _ = A.card := by simp [fins]

/-- The 106-cost construction actually needs at most 41 origins per signature. -/
theorem forestScheme_disclosureBound41 : forestScheme.DisclosureBound 41 := by
  intro i
  change (graph.disclosureOrigins (fins (setsName i))).card ≤ 41
  exact (card_disclosureOrigins_fins (isCut_setsName i).values).trans
    (card_le_of_mem_family (setsName_mem i))

/-- Membership in the public partial-disclosure framework. -/
theorem forestScheme_disclosureBound46 : forestScheme.DisclosureBound 46 := by
  intro i
  exact (forestScheme_disclosureBound41 i).trans (by decide)

/--
info: 'OptimalOTS.Forest.forestScheme_disclosureBound46' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms forestScheme_disclosureBound46

end OptimalOTS.Forest
