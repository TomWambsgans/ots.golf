import OptimalOTS.Disclosure
import Submissions.DisclosureLower.DisclosurePatterns
import Submissions.DisclosureLower.AveragedAssembly

/-!
# Verification lower bound for partial disclosures from at most 46 hash outputs

If every verification cost were at most 79, its reconstructed hash pattern would have at most
77 non-root hashes. The provenance limit bounds the number of distinct patterns by choose(123,46).
Averaging the signature-conversion attack over all pattern classes gives success at least
33/1000. Its complete experiment costs less than (33/1000) * 2^127, contradicting weak security.
The proof uses the existing bare oracle and forges on a message different from the signed one.
-/

namespace OptimalOTS

/-- The partial-disclosure restriction forces a verification costing at least 80. -/
theorem disclosureVerificationLowerBound_paper :
    DisclosureVerificationLowerBound paperParams 46 80 := by
  intro S hdis hS
  by_contra hn
  push Not at hn
  have hcost : ∀ i, S.verifyCost i ≤ 79 := fun i => Nat.lt_succ_iff.mp (hn i)
  have hrecon : ∀ i, S.graph.reconstructCost (S.sets i) ≤ 78 := by
    intro i
    have h := hcost i
    change 1 + S.graph.reconstructCost (S.sets i) ≤ 79 at h
    omega
  have hb := PatternAttack.cost_experiment S (2 ^ 122) 78 (by decide) hrecon
  have hsec := hS _ _ hb
  have hsuccess := AveragedAssembly.success_ge_count S
    (S.card_hashPattern_image_le_disclosure hdis hcost)
  exact (not_lt_of_ge hsuccess) (hsec.trans AveragedAssembly.budget_lt)

/-- The exported restricted lower-track certificate. -/
theorem Challenge.DisclosureLower.candidate :
    DisclosureVerificationLowerBound paperParams 46 80 :=
  disclosureVerificationLowerBound_paper

end OptimalOTS

/--
info: 'OptimalOTS.Challenge.DisclosureLower.candidate' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms OptimalOTS.Challenge.DisclosureLower.candidate
