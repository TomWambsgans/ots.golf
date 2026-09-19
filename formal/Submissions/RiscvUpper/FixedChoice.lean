import Submissions.RiscvUpper.Cuts
import Submissions.RiscvUpper.Valid

/-!
# The nibble layout

Reveal subtree digests 5 and 6, group digests 12, 13 and 14, and one value from each of chains
0 through 35. Chain `k < 32` is revealed at position `14 - d_k`, where `d_k` is nibble `k` of
the accepted index, and chains 32 to 35 at position 14. The remaining chain lengths sum to
`target`, so every disclosure set is a cut of the same cost, and distinct indices give distinct
cuts.
-/

namespace OptimalOTS.Forest

def fixedE : Finset (Fin 7) := {5, 6}
def fixedG : Finset (Fin 21) := {12, 13, 14}

theorem fixedE_card : fixedE.card = 2 := by decide
theorem fixedG_card : fixedG.card = 3 := by decide
theorem fixedG_allowed : fixedG ⊆ allowed fixedE := by decide

theorem fixed_active (k : Fin 63) : k ∈ active fixedE fixedG ↔ k.val < 36 := by
  simp only [active, fixedE, fixedG, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_insert, Finset.mem_singleton, subtreeOfChain, groupOfChain, Fin.ext_iff]
  omega

theorem nibble_le (i : Idx paperParams) (k : ℕ) (hk : k < 32) : nibble i.val k ≤ 14 :=
  (mem_validSet_accepted i.2).1 k (Finset.mem_range.mpr hk)

theorem nibble_sum (i : Idx paperParams) : ∑ k ∈ Finset.range 32, nibble i.val k = target :=
  (mem_validSet_accepted i.2).2

/-- The chain digits of an accepted index: its 32 nibbles, then four zeros. -/
def fixedDigits (i : Idx paperParams) (k : Fin 36) : Fin 15 :=
  if hk : k.val < 32 then ⟨nibble i.val k, Nat.lt_succ_of_le (nibble_le i k hk)⟩ else 0

/-- The digit function on naturals. -/
def digitAt (i : Idx paperParams) (k : ℕ) : ℕ := if k < 32 then nibble i.val k else 0

theorem fixedDigits_val (i : Idx paperParams) (k : Fin 36) :
    (fixedDigits i k).val = digitAt i k.val := by
  unfold fixedDigits digitAt
  split_ifs <;> rfl

theorem fixedDigits_sum (i : Idx paperParams) : ∑ k, (fixedDigits i k).val = target := by
  simp only [fixedDigits_val]
  rw [Fin.sum_univ_eq_sum_range (digitAt i) 36]
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
  simp only [digitAt, show ¬ 32 < 32 by omega, show ¬ 33 < 32 by omega, show ¬ 34 < 32 by omega,
    show ¬ 35 < 32 by omega, if_false, add_zero]
  rw [← nibble_sum i]
  exact Finset.sum_congr rfl fun k hk => if_pos (Finset.mem_range.mp hk)

theorem fixedDigits_injective : Function.Injective fixedDigits := by
  intro i j h
  apply Subtype.ext
  have hi : i.val < 16 ^ 32 := by rw [← idxBits_eq]; exact Idx.isLt i
  have hj : j.val < 16 ^ 32 := by rw [← idxBits_eq]; exact Idx.isLt j
  rw [← ofNibbles_nibble i.val 32 hi, ← ofNibbles_nibble j.val 32 hj]
  unfold ofNibbles
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' := Finset.mem_range.mp hk
  have e := congrArg (fun d : Fin 36 → Fin 15 => (d ⟨k, by omega⟩).val) h
  simp only [fixedDigits_val, digitAt, if_pos hk'] at e
  rw [e]

def fixedPositions (i : Idx paperParams) (k : Fin 63) : Fin 15 :=
  if hk : k.val < 36 then Fin.rev (fixedDigits i ⟨k.val, hk⟩) else 14

def fixedChoice (i : Idx paperParams) : Choice := (fixedE, fixedG, fixedPositions i)

theorem fixedPositions_normal (i : Idx paperParams) :
    ∀ k ∉ active fixedE fixedG, fixedPositions i k = 14 := by
  intro k hk
  simp only [fixedPositions, dif_neg (mt (fixed_active k).mpr hk)]

theorem fixedPositions_sum (i : Idx paperParams) :
    ∑ k ∈ active fixedE fixedG, (14 - (fixedPositions i k).val) = target := by
  rw [← fixedDigits_sum i]
  apply Finset.sum_bij (fun k hk => (⟨k.val, (fixed_active k).mp hk⟩ : Fin 36))
  · intro k hk; exact Finset.mem_univ _
  · intro k hk l hl h; exact Fin.ext (congrArg (fun v : Fin 36 => v.val) h)
  · intro k _
    refine ⟨⟨k.val, by omega⟩, (fixed_active _).mpr k.isLt, rfl⟩
  · intro k hk
    simp only [fixedPositions, dif_pos ((fixed_active k).mp hk), Fin.val_rev]
    have := (fixedDigits i ⟨k.val, (fixed_active k).mp hk⟩).isLt
    omega

theorem fixedPositions_mem (i : Idx paperParams) :
    fixedPositions i ∈ positions (active fixedE fixedG) target :=
  (mem_positions _ _ _).mpr ⟨fixedPositions_normal i, fixedPositions_sum i⟩

attribute [local irreducible] fixedDigits

theorem fixedCut_injective : Function.Injective (fun i => cutOf (fixedChoice i)) := by
  intro i j h
  have hc := cutOf_injective_of_normal (c := fixedChoice i) (c' := fixedChoice j)
    (fixedPositions_normal i) (fixedPositions_normal j) h
  apply fixedDigits_injective
  funext k
  have hp := congrFun (congrArg (fun c : Choice => c.2.2) hc) ⟨k.val, by omega⟩
  simpa [fixedChoice, fixedPositions, k.isLt] using hp

theorem fixedCut_isCut (i : Idx paperParams) : IsCut (cutOf (fixedChoice i)) :=
  isCut_cutOf_of_subset fixedG_allowed

theorem fixedCut_card (i : Idx paperParams) : (cutOf (fixedChoice i)).card ≤ 41 := by
  have h1 := Finset.card_union_le (fixedE.image Name.ev ∪ fixedG.image Name.gv)
    ((active fixedE fixedG).image fun k => chainNode k (fixedPositions i k))
  have h2 := Finset.card_union_le (fixedE.image Name.ev) (fixedG.image Name.gv)
  have h3 : (fixedE.image Name.ev).card ≤ fixedE.card := Finset.card_image_le
  have h4 : (fixedG.image Name.gv).card ≤ fixedG.card := Finset.card_image_le
  have h5 : ((active fixedE fixedG).image fun k => chainNode k (fixedPositions i k)).card ≤
      (active fixedE fixedG).card := Finset.card_image_le
  rw [card_active fixedE fixedG fixedG_allowed, fixedE_card, fixedG_card] at h5
  rw [fixedE_card] at h3
  rw [fixedG_card] at h4
  change (fixedE.image Name.ev ∪ fixedG.image Name.gv ∪
    (active fixedE fixedG).image (fun k => chainNode k (fixedPositions i k))).card ≤ 41
  omega

/-- Every disclosure set costs `target + 19 = 185` compressions to reconstruct. -/
theorem fixedCut_cost (i : Idx paperParams) :
    ∑ n ∈ evaluatedSet (cutOf (fixedChoice i)), n.cost = 185 := by
  rw [cost_cutOf_of_positions fixedG_allowed (fixedPositions_mem i)]
  change target + (21 - 3 * fixedE.card - fixedG.card) + (7 - fixedE.card) + 2 = 185
  rw [fixedE_card, fixedG_card]
  rfl

end OptimalOTS.Forest
