import Submissions.Lower.Patterns
import Submissions.Lower.SignFresh
import Submissions.Lower.CostCore

open OracleSpec OracleComp OracleComp.EvalDist ENNReal
noncomputable section
open scoped Classical

namespace OptimalOTS.PatternAttack

def goodIndices (S : Scheme paperParams) : Finset ℕ :=
  (Finset.univ.filter fun i => 8 ≤ (S.samePattern i).card).image Fin.val

theorem mem_goodIndices (S : Scheme paperParams) (i : Fin paperParams.numSets) :
    i.val ∈ goodIndices S ↔ 8 ≤ (S.samePattern i).card := by
  simp only [goodIndices, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨j, hj, hji⟩
    have he : j = i := Fin.ext hji
    simpa only [he] using hj
  · exact fun h => ⟨i, h, rfl⟩

theorem goodIndices_lt (S : Scheme paperParams) :
    ∀ n ∈ goodIndices S, n < paperParams.numSets := by
  intro n hn
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hn
  exact i.isLt

theorem card_goodIndices (S : Scheme paperParams) (hcost : ∀ i, S.verifyCost i ≤ 17) :
    3 * paperParams.numSets ≤ 4 * (goodIndices S).card := by
  have hb := S.card_small_samePattern_mul_four_le hcost
  have hs := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin paperParams.numSets)))
    (p := fun i => (S.samePattern i).card < 8)
  simp only [Finset.card_univ, Fintype.card_fin, not_lt] at hs
  unfold goodIndices
  rw [Finset.card_image_of_injective _ Fin.val_injective]
  omega

theorem cost_signIdx {P : Params} (S : Scheme P)
    (hidx : blockCost P (P.msgBits + P.nonceBits) = 1) (m : Message P) :
    CostAtMost P (signIdx P m) P.trialLimit := by
  have h := S.costAtMost_sign hidx (fun _ => 0) m
  rw [sign_eq_map] at h
  exact (costAtMost_map_iff _ _ _).mp h

end OptimalOTS.PatternAttack
