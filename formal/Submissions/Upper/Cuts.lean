import Submissions.Upper.Tree
import Submissions.Upper.Count

/-!
# The disclosure sets of the concrete scheme

A disclosure set is described by a *choice* `t : Fin 41 → Fin 21`: for every chain `k` the
position `t k ∈ {0, …, 20}` of the revealed chain value (`0` reveals the source `z_k`, `p ≥ 1`
reveals `c_{k,p} = cv k (p-1)`).  The verifier then recomputes `20 - t k` chain hashes on chain
`k`; the family consists of the choices with `∑ k, (20 - t k) = 96`, all of reconstruction cost
`11 + 96 = 107` with exactly `41` revealed values, and there are `comp 41 96 ≥ 2 ^ 115` of them
(`card_family`).
-/

open OracleSpec OracleComp ENNReal

noncomputable section

open scoped Classical

set_option linter.constructorNameAsVariable false

namespace OptimalOTS

namespace Flat

open Name

/-- The revealed node of chain `k` at position `p`. -/
def chainNode (k : Fin 41) (p : Fin 21) : Name :=
  if h : p.val = 0 then src k else cv k ⟨p.val - 1, by omega⟩

/-- Chain positions with total chain cost `s`.

Irreducible: the elaborator must never unfold `Finset.univ` of the function type `Fin 41 → Fin 21`
(it would try to enumerate it); use `positions_def` and `mem_positions`. -/
irreducible_def positions (s : ℕ) : Finset (Fin 41 → Fin 21) :=
  Finset.univ.filter fun t => ∑ k, (20 - (t k).val) = s

theorem mem_positions (s : ℕ) (t : Fin 41 → Fin 21) :
    t ∈ positions s ↔ ∑ k, (20 - (t k).val) = s := by
  rw [positions_def, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]

/-- A choice of disclosure set. -/
abbrev Choice := Fin 41 → Fin 21

/-- The disclosure set of a choice. -/
def cutOf (c : Choice) : Finset Name := Finset.univ.image fun k => chainNode k (c k)

/-- The admissible choices: chain cost `96`. -/
@[irreducible] def shapes : Finset Choice := positions 96

theorem mem_shapes_iff (c : Choice) : c ∈ shapes ↔ ∑ k, (20 - (c k).val) = 96 := by
  rw [shapes]
  exact mem_positions 96 c

/-- The family of disclosure sets. -/
@[irreducible] def family : Finset (Finset Name) := shapes.image cutOf

/-! ### Cardinality -/

theorem card_positions (s : ℕ) : (positions s).card = comp 41 s := by
  rw [← card_compSet]
  refine Finset.card_nbij' (fun t k => Fin.rev (t k)) (fun c k => Fin.rev (c k)) ?_ ?_ ?_ ?_
  · intro t ht
    rw [Finset.mem_coe, mem_positions] at ht
    rw [Finset.mem_coe, mem_compSet, ← ht]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Fin.val_rev]
    omega
  · intro c hc
    rw [Finset.mem_coe, mem_compSet] at hc
    rw [Finset.mem_coe, mem_positions, ← hc]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Fin.val_rev]
    omega
  · intro t _
    funext k
    simp only [Fin.rev_rev]
  · intro c _
    funext k
    simp only [Fin.rev_rev]

/-! ### Membership in a disclosure set -/

theorem chainNode_eq_src_iff (k k' : Fin 41) (p : Fin 21) :
    chainNode k p = src k' ↔ k = k' ∧ p = 0 := by
  unfold chainNode
  split_ifs with h
  · simp only [Name.src.injEq, Fin.ext_iff, Fin.val_zero, h, and_true]
  · simp only [false_iff, not_and, Fin.ext_iff, Fin.val_zero]
    intro _ hp
    exact h hp

theorem chainNode_eq_cv_iff (k k' : Fin 41) (p : Fin 21) (t : Fin 20) :
    chainNode k p = cv k' t ↔ k = k' ∧ p.val = t.val + 1 := by
  unfold chainNode
  split_ifs with h
  · simp only [false_iff, not_and]
    intro _
    omega
  · simp only [Name.cv.injEq, Fin.ext_iff]
    constructor
    · rintro ⟨hk, hp⟩
      exact ⟨hk, by omega⟩
    · rintro ⟨hk, hp⟩
      exact ⟨hk, by omega⟩

theorem chainNode_len (k : Fin 41) (p : Fin 21) : (chainNode k p).len = 128 := by
  unfold chainNode
  split_ifs <;> rfl

theorem mem_cutOf_iff (c : Choice) (n : Name) : n ∈ cutOf c ↔ ∃ k, chainNode k (c k) = n := by
  unfold cutOf
  simp only [Finset.mem_image, Finset.mem_univ, true_and]

theorem src_mem_cutOf_iff' (c : Choice) (k : Fin 41) : src k ∈ cutOf c ↔ c k = 0 := by
  rw [mem_cutOf_iff]
  constructor
  · rintro ⟨k', h⟩
    rw [chainNode_eq_src_iff] at h
    obtain ⟨rfl, h⟩ := h
    exact h
  · intro h
    exact ⟨k, (chainNode_eq_src_iff _ _ _).mpr ⟨rfl, h⟩⟩

theorem cv_mem_cutOf_iff' (c : Choice) (k : Fin 41) (t : Fin 20) :
    cv k t ∈ cutOf c ↔ (c k).val = t.val + 1 := by
  rw [mem_cutOf_iff]
  constructor
  · rintro ⟨k', h⟩
    rw [chainNode_eq_cv_iff] at h
    obtain ⟨rfl, h⟩ := h
    exact h
  · intro h
    exact ⟨k, (chainNode_eq_cv_iff _ _ _ _).mpr ⟨rfl, h⟩⟩

theorem not_mem_cutOf_of_len {c : Choice} {n : Name} (hn : n.len ≠ 128) : n ∉ cutOf c := by
  intro h
  rw [mem_cutOf_iff] at h
  obtain ⟨k, rfl⟩ := h
  exact hn (chainNode_len _ _)

theorem mem_cutOf_len' {c : Choice} {n : Name} (hn : n ∈ cutOf c) : n.len = 128 := by
  by_contra h
  exact not_mem_cutOf_of_len h hn

theorem ch_not_mem_cutOf (c : Choice) (k : Fin 41) (t : Fin 20) : ch k t ∉ cutOf c :=
  not_mem_cutOf_of_len (by simp [Name.len])

theorem rc_not_mem_cutOf (c : Choice) : rc ∉ cutOf c :=
  not_mem_cutOf_of_len (by simp [Name.len])

theorem rh_not_mem_cutOf (c : Choice) : rh ∉ cutOf c :=
  not_mem_cutOf_of_len (by simp [Name.len])

/-- The choice is determined by its disclosure set. -/
theorem cutOf_injective : Set.InjOn cutOf shapes := by
  intro c _ c' _ h
  funext k
  have hmem : chainNode k (c k) ∈ cutOf c' := by
    rw [← h, mem_cutOf_iff]
    exact ⟨k, rfl⟩
  unfold chainNode at hmem
  split_ifs at hmem with h0
  · rw [src_mem_cutOf_iff'] at hmem
    rw [hmem]
    exact Fin.ext h0
  · rw [cv_mem_cutOf_iff'] at hmem
    apply Fin.ext
    rw [hmem]
    dsimp only
    omega

theorem card_family : 2 ^ 115 ≤ family.card := by
  unfold family
  rw [Finset.card_image_of_injOn cutOf_injective]
  unfold shapes
  rw [card_positions]
  exact count_ge

/-! ### Evaluated nodes -/

theorem forall_above_of_child {A : Finset Name} {n p : Name} (hp : child n = some p)
    (he : Evaluated A p) : ∀ m, Above m n → m ∉ A := by
  intro m hm
  rw [above_of_child hp] at hm
  rcases hm with rfl | hm
  · exact he.1
  · exact he.2 m hm

theorem evaluated_of_child {A : Finset Name} {n p : Name} (hp : child n = some p) (hn : n ∉ A)
    (he : Evaluated A p) : Evaluated A n :=
  ⟨hn, forall_above_of_child hp he⟩

theorem evaluated_rh' (c : Choice) : Evaluated (cutOf c) rh :=
  ⟨rh_not_mem_cutOf c, fun m hm => absurd hm (not_above_rh m)⟩

theorem evaluated_rc' (c : Choice) : Evaluated (cutOf c) rc :=
  evaluated_of_child rfl (rc_not_mem_cutOf c) (evaluated_rh' c)

theorem evaluated_ch_iff' (c : Choice) (k : Fin 41) (t : Fin 20) :
    Evaluated (cutOf c) (ch k t) ↔ (c k).val ≤ t.val := by
  unfold Evaluated
  simp only [above_iff_mem_ancSet, ancSet, Finset.forall_mem_union, Finset.forall_mem_image,
    Finset.mem_filter, Finset.mem_univ, true_and, Finset.forall_mem_insert, Finset.mem_singleton,
    forall_eq, ch_not_mem_cutOf, cv_mem_cutOf_iff', rc_not_mem_cutOf, rh_not_mem_cutOf,
    not_false_eq_true, true_and, and_true, implies_true]
  constructor
  · intro h1
    by_contra hlt
    have hv := (c k).isLt
    exact @h1 ⟨(c k).val - 1, by omega⟩ (by rw [Fin.le_def]; dsimp only; omega) (by dsimp only; omega)
  · intro hle x hx
    rw [Fin.le_def] at hx
    omega

theorem child_cv_of_lt (k : Fin 41) (t : Fin 20) (ht : t.val < 19) :
    child (cv k t) = some (ch k ⟨t.val + 1, by omega⟩) := by
  simp only [Name.child]
  rw [dif_neg (by omega)]

theorem child_cv_of_eq (k : Fin 41) (t : Fin 20) (ht : t.val = 19) : child (cv k t) = some rc := by
  simp only [Name.child]
  rw [dif_pos ht]

theorem isCut_cutOf' (c : Choice) : IsCut (cutOf c) where
  values _ hn := mem_cutOf_len' hn
  antichain := by
    intro n hn
    rw [mem_cutOf_iff] at hn
    obtain ⟨k, rfl⟩ := hn
    unfold chainNode
    split_ifs with h0
    · exact forall_above_of_child rfl
        ((evaluated_ch_iff' c k 0).mpr (by rw [h0]; exact Nat.zero_le _))
    · by_cases h20 : (c k).val = 20
      · exact forall_above_of_child (child_cv_of_eq k _ (by dsimp only; omega)) (evaluated_rc' c)
      · have hlt := (c k).isLt
        refine forall_above_of_child (child_cv_of_lt k _ (by dsimp only; omega))
          ((evaluated_ch_iff' c k _).mpr ?_)
        dsimp only
        omega
  covers := by
    intro k
    by_cases h0 : (c k).val = 0
    · exact Or.inl ((src_mem_cutOf_iff' c k).mpr (Fin.ext h0))
    · have hlt := (c k).isLt
      refine Or.inr ⟨cv k ⟨(c k).val - 1, by omega⟩,
        (cv_mem_cutOf_iff' c k _).mpr (by dsimp only; omega), ?_⟩
      rw [above_iff_mem_ancSet]
      simp [ancSet]

theorem card_cutOf_le' (c : Choice) : (cutOf c).card ≤ 41 := by
  unfold cutOf
  exact Finset.card_image_le.trans (by simp)

theorem sum_fin20_ge (v : ℕ) : ∑ t : Fin 20, (if v ≤ t.val then 1 else 0) = 20 - v := by
  rw [Fin.sum_univ_eq_sum_range (fun t => if v ≤ t then 1 else 0) 20, ← Finset.card_filter]
  have : (Finset.range 20).filter (fun t => v ≤ t) = Finset.Ico v 20 := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  rw [this, Nat.card_Ico]

theorem cost_cutOf' {c : Choice} (hc : c ∈ shapes) :
    ∑ n ∈ evaluatedSet (cutOf c), n.cost = 107 := by
  rw [mem_shapes_iff] at hc
  have h_ch : ∑ k, ∑ t, (if Evaluated (cutOf c) (ch k t) then 1 else 0) = 96 := by
    simp only [evaluated_ch_iff']
    simp only [sum_fin20_ge]
    exact hc
  rw [evaluatedSet, Finset.sum_filter, Name.sum_eq]
  simp only [Name.cost, ite_self, Finset.sum_const_zero, zero_add, add_zero]
  rw [if_pos (evaluated_rh' c), h_ch]

/-! ## Membership in a disclosure set -/

section props

variable {c : Choice} (hc : c ∈ shapes)
include hc

-- the statements below take `hc` for uniformity; some proofs do not need it
set_option linter.unusedSectionVars false

theorem src_mem_cutOf_iff (k : Fin 41) : src k ∈ cutOf c ↔ c k = 0 :=
  src_mem_cutOf_iff' c k

theorem cv_mem_cutOf_iff (k : Fin 41) (t : Fin 20) : cv k t ∈ cutOf c ↔ (c k).val = t.val + 1 :=
  cv_mem_cutOf_iff' c k t

theorem mem_cutOf_len (n : Name) (hn : n ∈ cutOf c) : n.len = 128 :=
  mem_cutOf_len' hn

/-- Which hash nodes are evaluated. -/
theorem evaluated_rh : Evaluated (cutOf c) rh :=
  evaluated_rh' c

theorem evaluated_ch_iff (k : Fin 41) (t : Fin 20) :
    Evaluated (cutOf c) (ch k t) ↔ (c k).val ≤ t.val :=
  evaluated_ch_iff' c k t

theorem isCut_cutOf : IsCut (cutOf c) :=
  isCut_cutOf' c

theorem card_cutOf_le : (cutOf c).card ≤ 41 :=
  card_cutOf_le' c

theorem cost_cutOf : ∑ n ∈ evaluatedSet (cutOf c), n.cost = 107 :=
  cost_cutOf' hc

end props

theorem mem_family_iff (A : Finset Name) : A ∈ family ↔ ∃ c ∈ shapes, cutOf c = A := by
  unfold family
  exact Finset.mem_image

theorem isCut_of_mem_family {A : Finset Name} (h : A ∈ family) : IsCut A := by
  unfold family at h
  rw [Finset.mem_image] at h
  obtain ⟨c, hc, hA⟩ := h
  rw [← hA]
  exact isCut_cutOf hc

theorem card_le_of_mem_family {A : Finset Name} (h : A ∈ family) : A.card ≤ 41 := by
  unfold family at h
  rw [Finset.mem_image] at h
  obtain ⟨c, hc, hA⟩ := h
  rw [← hA]
  exact card_cutOf_le hc

theorem cost_of_mem_family {A : Finset Name} (h : A ∈ family) :
    ∑ n ∈ evaluatedSet A, n.cost = 107 := by
  unfold family at h
  rw [Finset.mem_image] at h
  obtain ⟨c, hc, hA⟩ := h
  rw [← hA]
  exact cost_cutOf hc

end Flat

end OptimalOTS
