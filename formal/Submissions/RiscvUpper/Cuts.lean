import Submissions.RiscvUpper.Tree
import Submissions.RiscvUpper.Count

/-!
# Disclosure sets of the forest

A disclosure set is described by a *choice* `(E, G, t)`: the revealed subtree digests `E`, the
revealed group digests `G` (under evaluated subtrees), and for every chain `k` the position
`t k ∈ {0, …, 14}` of the revealed chain value (`0` reveals the source `z_k`, `p ≥ 1` reveals
`c_{k,p} = cv k (p-1)`); only *active* chains (under evaluated groups and subtrees) reveal a
value, and inactive chains have `t k = 14` so that the choice is determined by the set
(`cutOf_injective_of_normal`).

`cutOf c` is a cut whenever `G` lies under unevaluated subtrees (`isCut_cutOf_of_subset`), and
its reconstruction cost is fixed by the total chain cost of the positions
(`cost_cutOf_of_positions`). `FixedChoice.lean` instantiates this with the nibble layout.
-/

open OracleSpec OracleComp ENNReal

noncomputable section

open scoped Classical

set_option linter.constructorNameAsVariable false

namespace OptimalOTS

namespace Forest

open Name

/-- The subtree of a group. -/
def subtreeOf (j : Fin 21) : Fin 7 := ⟨j / 3, by omega⟩

/-- The group of a chain. -/
def groupOfChain (k : Fin 63) : Fin 21 := ⟨k / 3, by omega⟩

/-- The subtree of a chain. -/
def subtreeOfChain (k : Fin 63) : Fin 7 := ⟨k / 9, by omega⟩

/-- Groups under evaluated subtrees. -/
def allowed (E : Finset (Fin 7)) : Finset (Fin 21) := Finset.univ.filter fun j => subtreeOf j ∉ E

/-- Chains under evaluated groups and subtrees. -/
def active (E : Finset (Fin 7)) (G : Finset (Fin 21)) : Finset (Fin 63) :=
  Finset.univ.filter fun k => subtreeOfChain k ∉ E ∧ groupOfChain k ∉ G

/-- The revealed node of chain `k` at position `p`. -/
def chainNode (k : Fin 63) (p : Fin 15) : Name :=
  if h : p.val = 0 then src k else cv k ⟨p.val - 1, by omega⟩

/-- Chain positions with total chain cost `s` on the chains of `S`; other chains are at `14`.

Irreducible: the elaborator must never unfold `Finset.univ` of the function type `Fin 63 → Fin 15`
(it would try to enumerate it); use `positions_def` and `mem_positions`. -/
irreducible_def positions (S : Finset (Fin 63)) (s : ℕ) : Finset (Fin 63 → Fin 15) :=
  Finset.univ.filter fun t => (∀ k ∉ S, t k = 14) ∧ ∑ k ∈ S, (14 - (t k).val) = s

theorem mem_positions (S : Finset (Fin 63)) (s : ℕ) (t : Fin 63 → Fin 15) :
    t ∈ positions S s ↔ (∀ k ∉ S, t k = 14) ∧ ∑ k ∈ S, (14 - (t k).val) = s := by
  rw [positions_def, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]

/-- A choice of disclosure set. -/
abbrev Choice := Finset (Fin 7) × Finset (Fin 21) × (Fin 63 → Fin 15)

/-- The disclosure set of a choice. -/
def cutOf (c : Choice) : Finset Name :=
  c.1.image ev ∪ c.2.1.image gv ∪ (active c.1 c.2.1).image fun k => chainNode k (c.2.2 k)

/-! ### Cardinalities of the index sets -/

theorem subtreeOf_groupOf (l : Fin 7) (a : Fin 3) : subtreeOf (groupOf l a) = l := by
  apply Fin.ext
  simp only [subtreeOf, groupOf]
  omega

theorem groupOf_injective : Function.Injective fun p : Fin 7 × Fin 3 => groupOf p.1 p.2 := by
  rintro ⟨l, a⟩ ⟨l', a'⟩ h
  simp only [groupOf, Fin.mk.injEq] at h
  have hl : l = l' := Fin.ext (by omega)
  have ha : a = a' := Fin.ext (by omega)
  rw [hl, ha]

theorem allowed_eq_image (E : Finset (Fin 7)) :
    allowed E = (Eᶜ ×ˢ (Finset.univ : Finset (Fin 3))).image fun p => groupOf p.1 p.2 := by
  ext j
  simp only [allowed, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
    Finset.mem_product, Finset.mem_compl, and_true, Prod.exists]
  constructor
  · intro h
    refine ⟨subtreeOf j, ⟨j % 3, by omega⟩, h, ?_⟩
    apply Fin.ext
    simp only [groupOf, subtreeOf]
    omega
  · rintro ⟨l, a, hl, rfl⟩
    rwa [subtreeOf_groupOf]

theorem card_allowed (E : Finset (Fin 7)) : (allowed E).card = 21 - 3 * E.card := by
  rw [allowed_eq_image, Finset.card_image_of_injective _ groupOf_injective, Finset.card_product,
    Finset.card_compl, Finset.card_univ, Fintype.card_fin, Fintype.card_fin]
  have := Finset.card_le_univ E
  rw [Fintype.card_fin] at this
  omega

theorem groupOfChain_chainOf (j : Fin 21) (a : Fin 3) : groupOfChain (chainOf j a) = j := by
  apply Fin.ext
  simp only [groupOfChain, chainOf]
  omega

theorem subtreeOfChain_eq (k : Fin 63) : subtreeOfChain k = subtreeOf (groupOfChain k) := by
  apply Fin.ext
  simp only [subtreeOfChain, subtreeOf, groupOfChain]
  omega

theorem chainOf_injective : Function.Injective fun p : Fin 21 × Fin 3 => chainOf p.1 p.2 := by
  rintro ⟨j, a⟩ ⟨j', a'⟩ h
  simp only [chainOf, Fin.mk.injEq] at h
  have hj : j = j' := Fin.ext (by omega)
  have ha : a = a' := Fin.ext (by omega)
  rw [hj, ha]

theorem mem_active_iff (E : Finset (Fin 7)) (G : Finset (Fin 21)) (k : Fin 63) :
    k ∈ active E G ↔ subtreeOfChain k ∉ E ∧ groupOfChain k ∉ G := by
  simp only [active, Finset.mem_filter, Finset.mem_univ, true_and]

theorem active_eq_image (E : Finset (Fin 7)) (G : Finset (Fin 21)) :
    active E G =
      ((allowed E \ G) ×ˢ (Finset.univ : Finset (Fin 3))).image fun p => chainOf p.1 p.2 := by
  ext k
  simp only [active, allowed, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
    Finset.mem_product, Finset.mem_sdiff, and_true, Prod.exists]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨groupOfChain k, ⟨k % 3, by omega⟩, ⟨?_, h2⟩, ?_⟩
    · rwa [← subtreeOfChain_eq]
    · apply Fin.ext
      simp only [chainOf, groupOfChain]
      omega
  · rintro ⟨j, a, ⟨h1, h2⟩, rfl⟩
    rw [subtreeOfChain_eq, groupOfChain_chainOf]
    exact ⟨h1, h2⟩

theorem card_active (E : Finset (Fin 7)) (G : Finset (Fin 21)) (hG : G ⊆ allowed E) :
    (active E G).card = 3 * (21 - 3 * E.card - G.card) := by
  rw [active_eq_image, Finset.card_image_of_injective _ chainOf_injective, Finset.card_product,
    Finset.card_sdiff_of_subset hG, card_allowed, Finset.card_univ, Fintype.card_fin]
  omega

/-! ### Membership in a disclosure set -/

theorem chainNode_eq_src_iff (k k' : Fin 63) (p : Fin 15) :
    chainNode k p = src k' ↔ k = k' ∧ p = 0 := by
  unfold chainNode
  split_ifs with h
  · simp only [Name.src.injEq, Fin.ext_iff, Fin.val_zero, h, and_true]
  · simp only [false_iff, not_and, Fin.ext_iff, Fin.val_zero]
    intro _ hp
    exact h hp

theorem chainNode_eq_cv_iff (k k' : Fin 63) (p : Fin 15) (t : Fin 14) :
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

theorem chainNode_ne_ev (k : Fin 63) (p : Fin 15) (l : Fin 7) : chainNode k p ≠ ev l := by
  unfold chainNode
  split_ifs <;> simp

theorem chainNode_ne_gv (k : Fin 63) (p : Fin 15) (j : Fin 21) : chainNode k p ≠ gv j := by
  unfold chainNode
  split_ifs <;> simp

theorem chainNode_len (k : Fin 63) (p : Fin 15) : (chainNode k p).len = 128 := by
  unfold chainNode
  split_ifs <;> rfl

theorem mem_cutOf_iff (c : Choice) (n : Name) :
    n ∈ cutOf c ↔ (∃ l ∈ c.1, ev l = n) ∨ (∃ j ∈ c.2.1, gv j = n) ∨
      ∃ k ∈ active c.1 c.2.1, chainNode k (c.2.2 k) = n := by
  unfold cutOf
  simp only [Finset.mem_union, Finset.mem_image, or_assoc]

theorem ev_mem_cutOf_iff (c : Choice) (l : Fin 7) : ev l ∈ cutOf c ↔ l ∈ c.1 := by
  rw [mem_cutOf_iff]
  constructor
  · rintro (⟨l', hl', h⟩ | ⟨j, _, h⟩ | ⟨k, _, h⟩)
    · rw [Name.ev.injEq] at h
      exact h ▸ hl'
    · exact absurd h (by simp)
    · exact absurd h (chainNode_ne_ev _ _ _)
  · intro h
    exact Or.inl ⟨l, h, rfl⟩

theorem gv_mem_cutOf_iff (c : Choice) (j : Fin 21) : gv j ∈ cutOf c ↔ j ∈ c.2.1 := by
  rw [mem_cutOf_iff]
  constructor
  · rintro (⟨l, _, h⟩ | ⟨j', hj', h⟩ | ⟨k, _, h⟩)
    · exact absurd h (by simp)
    · rw [Name.gv.injEq] at h
      exact h ▸ hj'
    · exact absurd h (chainNode_ne_gv _ _ _)
  · intro h
    exact Or.inr (Or.inl ⟨j, h, rfl⟩)

theorem src_mem_cutOf_iff (c : Choice) (k : Fin 63) :
    src k ∈ cutOf c ↔ k ∈ active c.1 c.2.1 ∧ c.2.2 k = 0 := by
  rw [mem_cutOf_iff]
  constructor
  · rintro (⟨l, _, h⟩ | ⟨j, _, h⟩ | ⟨k', hk', h⟩)
    · exact absurd h (by simp)
    · exact absurd h (by simp)
    · rw [chainNode_eq_src_iff] at h
      obtain ⟨rfl, h⟩ := h
      exact ⟨hk', h⟩
  · rintro ⟨hk, h⟩
    exact Or.inr (Or.inr ⟨k, hk, (chainNode_eq_src_iff _ _ _).mpr ⟨rfl, h⟩⟩)

theorem cv_mem_cutOf_iff (c : Choice) (k : Fin 63) (t : Fin 14) :
    cv k t ∈ cutOf c ↔ k ∈ active c.1 c.2.1 ∧ (c.2.2 k).val = t.val + 1 := by
  rw [mem_cutOf_iff]
  constructor
  · rintro (⟨l, _, h⟩ | ⟨j, _, h⟩ | ⟨k', hk', h⟩)
    · exact absurd h (by simp)
    · exact absurd h (by simp)
    · rw [chainNode_eq_cv_iff] at h
      obtain ⟨rfl, h⟩ := h
      exact ⟨hk', h⟩
  · rintro ⟨hk, h⟩
    exact Or.inr (Or.inr ⟨k, hk, (chainNode_eq_cv_iff _ _ _ _).mpr ⟨rfl, h⟩⟩)

theorem not_mem_cutOf_of_len {c : Choice} {n : Name} (hn : n.len ≠ 128) : n ∉ cutOf c := by
  intro h
  rw [mem_cutOf_iff] at h
  rcases h with ⟨l, _, rfl⟩ | ⟨j, _, rfl⟩ | ⟨k, _, rfl⟩
  · exact hn rfl
  · exact hn rfl
  · exact hn (chainNode_len _ _)

theorem mem_cutOf_len {c : Choice} {n : Name} (hn : n ∈ cutOf c) : n.len = 128 := by
  by_contra h
  exact not_mem_cutOf_of_len h hn

theorem ci_not_mem_cutOf (c : Choice) (k : Fin 63) (t : Fin 14) : ci k t ∉ cutOf c :=
  not_mem_cutOf_of_len (by simp [Name.len])

theorem ch_not_mem_cutOf (c : Choice) (k : Fin 63) (t : Fin 14) : ch k t ∉ cutOf c :=
  not_mem_cutOf_of_len (by simp [Name.len])

theorem gc_not_mem_cutOf (c : Choice) (j : Fin 21) : gc j ∉ cutOf c :=
  not_mem_cutOf_of_len (by simp [Name.len])

theorem gh_not_mem_cutOf (c : Choice) (j : Fin 21) : gh j ∉ cutOf c :=
  not_mem_cutOf_of_len (by simp [Name.len])

theorem ec_not_mem_cutOf (c : Choice) (l : Fin 7) : ec l ∉ cutOf c :=
  not_mem_cutOf_of_len (by simp [Name.len])

theorem eh_not_mem_cutOf (c : Choice) (l : Fin 7) : eh l ∉ cutOf c :=
  not_mem_cutOf_of_len (by simp [Name.len])

theorem rc_not_mem_cutOf (c : Choice) : rc ∉ cutOf c :=
  not_mem_cutOf_of_len (by simp [Name.len])

theorem rh_not_mem_cutOf (c : Choice) : rh ∉ cutOf c :=
  not_mem_cutOf_of_len (by simp [Name.len])

/-! ### Injectivity -/

/-- The choice is determined by its disclosure set. -/
theorem cutOf_injective_of_normal {c c' : Choice}
    (hc : ∀ k ∉ active c.1 c.2.1, c.2.2 k = 14)
    (hc' : ∀ k ∉ active c'.1 c'.2.1, c'.2.2 k = 14)
    (h : cutOf c = cutOf c') : c = c' := by
  have hE : c.1 = c'.1 := by
    ext l
    rw [← ev_mem_cutOf_iff c l, ← ev_mem_cutOf_iff c' l, h]
  have hG : c.2.1 = c'.2.1 := by
    ext j
    rw [← gv_mem_cutOf_iff c j, ← gv_mem_cutOf_iff c' j, h]
  have ht : c.2.2 = c'.2.2 := by
    funext k
    by_cases hk : k ∈ active c.1 c.2.1
    · have hmem : chainNode k (c.2.2 k) ∈ cutOf c' := by
        rw [← h, mem_cutOf_iff]
        exact Or.inr (Or.inr ⟨k, hk, rfl⟩)
      unfold chainNode at hmem
      split_ifs at hmem with h0
      · rw [src_mem_cutOf_iff] at hmem
        rw [hmem.2]
        exact Fin.ext h0
      · rw [cv_mem_cutOf_iff] at hmem
        apply Fin.ext
        rw [hmem.2]
        dsimp only
        omega
    · rw [hc k hk, hc' k (by rwa [← hE, ← hG])]
  exact Prod.ext hE (Prod.ext hG ht)

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

theorem evaluated_rh (c : Choice) : Evaluated (cutOf c) rh :=
  ⟨rh_not_mem_cutOf c, fun m hm => absurd hm (not_above_rh m)⟩

theorem evaluated_rc (c : Choice) : Evaluated (cutOf c) rc :=
  evaluated_of_child rfl (rc_not_mem_cutOf c) (evaluated_rh c)

theorem evaluated_eh_iff (c : Choice) (l : Fin 7) : Evaluated (cutOf c) (eh l) ↔ l ∉ c.1 := by
  constructor
  · intro h
    rw [← ev_mem_cutOf_iff c l]
    exact h.2 (ev l) (Above.child rfl)
  · intro hl
    refine evaluated_of_child rfl (eh_not_mem_cutOf c l) ?_
    refine evaluated_of_child rfl ?_ (evaluated_rc c)
    rw [ev_mem_cutOf_iff]
    exact hl

theorem evaluated_gh_iff (c : Choice) (j : Fin 21) :
    Evaluated (cutOf c) (gh j) ↔ subtreeOf j ∉ c.1 ∧ j ∉ c.2.1 := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · rw [← ev_mem_cutOf_iff c]
      refine h.2 (ev (subtreeOf j)) ((above_iff_mem_ancSet _ _).mpr ?_)
      simp [ancSet, subtreeOf]
    · rw [← gv_mem_cutOf_iff c j]
      exact h.2 (gv j) (Above.child rfl)
  · rintro ⟨h1, h2⟩
    refine evaluated_of_child rfl (gh_not_mem_cutOf c j) ?_
    refine evaluated_of_child rfl ?_ ?_
    · rw [gv_mem_cutOf_iff]
      exact h2
    · refine evaluated_of_child rfl (ec_not_mem_cutOf c _) ?_
      rw [evaluated_eh_iff]
      exact h1

theorem evaluated_ch_iff (c : Choice) (k : Fin 63) (t : Fin 14) :
    Evaluated (cutOf c) (ch k t) ↔ k ∈ active c.1 c.2.1 ∧ (c.2.2 k).val ≤ t.val := by
  unfold Evaluated
  simp only [above_iff_mem_ancSet, ancSet, Finset.forall_mem_union, Finset.forall_mem_image,
    Finset.mem_filter, Finset.mem_univ, true_and, Finset.forall_mem_insert, Finset.mem_singleton,
    forall_eq, ci_not_mem_cutOf, ch_not_mem_cutOf, cv_mem_cutOf_iff, gc_not_mem_cutOf,
    gh_not_mem_cutOf,
    gv_mem_cutOf_iff, ec_not_mem_cutOf, eh_not_mem_cutOf, ev_mem_cutOf_iff, rc_not_mem_cutOf,
    rh_not_mem_cutOf, not_false_eq_true, true_and, and_true, implies_true, mem_active_iff,
    subtreeOfChain, groupOfChain]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨⟨h3, h2⟩, ?_⟩
    by_contra hlt
    have hv := (c.2.2 k).isLt
    exact @h1 ⟨(c.2.2 k).val - 1, by omega⟩ (by rw [Fin.le_def]; dsimp only; omega)
      ⟨⟨h3, h2⟩, by dsimp only; omega⟩
  · rintro ⟨⟨h3, h2⟩, hle⟩
    refine ⟨fun x hx h => ?_, h2, h3⟩
    rw [Fin.le_def] at hx
    omega

/-- The input of a chain hash is evaluated exactly when the chain hash is. -/
theorem evaluated_ci_iff (c : Choice) (k : Fin 63) (t : Fin 14) :
    Evaluated (cutOf c) (ci k t) ↔ k ∈ active c.1 c.2.1 ∧ (c.2.2 k).val ≤ t.val := by
  rw [← evaluated_ch_iff]
  constructor
  · intro h
    exact ⟨ch_not_mem_cutOf c k t, fun m hm => h.2 m (Above.step rfl hm)⟩
  · intro h
    exact evaluated_of_child rfl (ci_not_mem_cutOf c k t) h

theorem child_cv_of_lt (k : Fin 63) (t : Fin 14) (ht : t.val < 13) :
    child (cv k t) = some (ci k ⟨t.val + 1, by omega⟩) := by
  simp only [Name.child]
  rw [dif_neg (by omega)]

theorem child_cv_of_eq (k : Fin 63) (t : Fin 14) (ht : t.val = 13) :
    child (cv k t) = some (gc (groupOfChain k)) := by
  simp only [Name.child]
  rw [dif_pos ht]
  rfl

theorem isCut_cutOf_of_subset {c : Choice} (hG : c.2.1 ⊆ allowed c.1) : IsCut (cutOf c) where
  values _ hn := mem_cutOf_len hn
  antichain := by
    intro n hn
    rw [mem_cutOf_iff] at hn
    rcases hn with ⟨l, hl, rfl⟩ | ⟨j, hj, rfl⟩ | ⟨k, hk, rfl⟩
    · exact forall_above_of_child rfl (evaluated_rc c)
    · refine forall_above_of_child rfl (evaluated_of_child rfl (ec_not_mem_cutOf c _)
        ((evaluated_eh_iff c _).mpr ?_))
      have := hG hj
      simp only [allowed, Finset.mem_filter, Finset.mem_univ, true_and] at this
      exact this
    · have hk' := (mem_active_iff _ _ _).mp hk
      unfold chainNode
      split_ifs with h0
      · exact forall_above_of_child rfl
          ((evaluated_ci_iff c k 0).mpr ⟨hk, by rw [h0]; exact Nat.zero_le _⟩)
      · by_cases h13 : (c.2.2 k).val = 14
        · refine forall_above_of_child (child_cv_of_eq k _ (by dsimp only; omega))
            (evaluated_of_child rfl (gc_not_mem_cutOf c _) ((evaluated_gh_iff c _).mpr ?_))
          rw [← subtreeOfChain_eq]
          exact hk'
        · have hlt := (c.2.2 k).isLt
          refine forall_above_of_child (child_cv_of_lt k _ (by dsimp only; omega))
            ((evaluated_ci_iff c k _).mpr ⟨hk, ?_⟩)
          dsimp only
          omega
  covers := by
    intro k
    by_cases hk : k ∈ active c.1 c.2.1
    · by_cases h0 : (c.2.2 k).val = 0
      · exact Or.inl ((src_mem_cutOf_iff c k).mpr ⟨hk, Fin.ext h0⟩)
      · have hlt := (c.2.2 k).isLt
        refine Or.inr ⟨cv k ⟨(c.2.2 k).val - 1, by omega⟩,
          (cv_mem_cutOf_iff c k _).mpr ⟨hk, by dsimp only; omega⟩, ?_⟩
        rw [above_iff_mem_ancSet]
        simp [ancSet]
    · rw [mem_active_iff, not_and_or, not_not, not_not] at hk
      rcases hk with hk | hk
      · refine Or.inr ⟨ev (subtreeOfChain k), (ev_mem_cutOf_iff c _).mpr hk, ?_⟩
        rw [above_iff_mem_ancSet]
        simp [ancSet, subtreeOfChain]
      · refine Or.inr ⟨gv (groupOfChain k), (gv_mem_cutOf_iff c _).mpr hk, ?_⟩
        rw [above_iff_mem_ancSet]
        simp [ancSet, groupOfChain]

theorem sum_fin14_ge (v : ℕ) : ∑ t : Fin 14, (if v ≤ t.val then 1 else 0) = 14 - v := by
  rw [Fin.sum_univ_eq_sum_range (fun t => if v ≤ t then 1 else 0) 14, ← Finset.card_filter]
  have : (Finset.range 14).filter (fun t => v ≤ t) = Finset.Ico v 14 := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  rw [this, Nat.card_Ico]

theorem cost_cutOf_of_positions {c : Choice} {s : ℕ}
    (hG : c.2.1 ⊆ allowed c.1) (ht : c.2.2 ∈ positions (active c.1 c.2.1) s) :
    ∑ n ∈ evaluatedSet (cutOf c), n.cost =
      s + (21 - 3 * c.1.card - c.2.1.card) + (7 - c.1.card) + 2 := by
  let a := c.1.card
  let b := c.2.1.card
  have ha : c.1.card = a := rfl
  have hb : c.2.1.card = b := rfl
  have h_eh : ∑ l, (if Evaluated (cutOf c) (eh l) then 1 else 0) = 7 - a := by
    simp only [evaluated_eh_iff]
    rw [← Finset.card_filter]
    have : (Finset.univ.filter fun l => l ∉ c.1) = c.1ᶜ := by
      ext l
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_compl]
    rw [this, Finset.card_compl, Fintype.card_fin, ha]
  have h_gh : ∑ j, (if Evaluated (cutOf c) (gh j) then 1 else 0) = 21 - 3 * a - b := by
    simp only [evaluated_gh_iff]
    rw [← Finset.card_filter]
    have : (Finset.univ.filter fun j => subtreeOf j ∉ c.1 ∧ j ∉ c.2.1) = allowed c.1 \ c.2.1 := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff, allowed]
    rw [this, Finset.card_sdiff_of_subset hG, card_allowed, ha, hb]
  have h_ch : ∑ k, ∑ t, (if Evaluated (cutOf c) (ch k t) then 1 else 0) = s := by
    simp only [evaluated_ch_iff]
    have hin : ∀ k, ∑ t : Fin 14, (if k ∈ active c.1 c.2.1 ∧ (c.2.2 k).val ≤ t.val then 1 else 0) =
        if k ∈ active c.1 c.2.1 then 14 - (c.2.2 k).val else 0 := by
      intro k
      by_cases hk : k ∈ active c.1 c.2.1
      · simp only [hk, true_and, if_true]
        exact sum_fin14_ge _
      · simp only [hk, false_and, if_false, Finset.sum_const_zero]
    simp only [hin]
    rw [Finset.sum_ite_mem, Finset.univ_inter]
    exact ((mem_positions _ _ _).mp ht).2
  rw [evaluatedSet, Finset.sum_filter, Name.sum_eq]
  simp only [Name.cost, ite_self, Finset.sum_const_zero, zero_add, add_zero]
  rw [if_pos (evaluated_rh c), h_ch, h_gh, h_eh]

end Forest

end OptimalOTS
