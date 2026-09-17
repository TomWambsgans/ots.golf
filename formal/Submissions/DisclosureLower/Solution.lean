import OptimalOTS.WholeWords
import Submissions.DisclosureLower.WholeWordOrigins
import Submissions.DisclosureLower.AveragedAssembly

/-!
# Verification lower bound for whole-word DAGs

A 5248-bit payload contains at most 41 whole 128-bit words and therefore represents at most
41 hash origins. If every verification cost were at most 92, its pattern would have at most
90 non-root hashes. There are at most choose(131,41) distinct patterns. The averaged
signature-conversion attack succeeds with probability at least 9801/280000, exceeding its
complete experiment budget divided by 2^127. Its forgery uses a different message.
-/

namespace OptimalOTS

/-- Whole-word operations force a verification costing at least 93. -/
theorem wholeWordVerificationLowerBound_paper :
    WholeWordVerificationLowerBound paperParams 93 := by
  intro S hwords hS
  have hdis := S.disclosureBound41_of_wholeWords hwords
  by_contra hn
  push Not at hn
  have hcost : ∀ i, S.verifyCost i ≤ 92 := fun i => Nat.lt_succ_iff.mp (hn i)
  have hrecon : ∀ i, S.graph.reconstructCost (S.sets i) ≤ 91 := by
    intro i
    have h := hcost i
    change 1 + S.graph.reconstructCost (S.sets i) ≤ 92 at h
    omega
  have hb := PatternAttack.cost_experiment S (2 ^ 122) 91 (by decide) hrecon
  have hsec := hS _ _ hb
  have hsuccess := AveragedAssembly.success_ge_count S
    (S.card_hashPattern_image_le_disclosure hdis hcost)
  exact (not_lt_of_ge hsuccess) (hsec.trans AveragedAssembly.budget_lt)

/-- The exported restricted lower-track certificate. -/
theorem Challenge.DisclosureLower.candidate :
    WholeWordVerificationLowerBound paperParams 93 :=
  wholeWordVerificationLowerBound_paper

end OptimalOTS

/--
info: 'OptimalOTS.Challenge.DisclosureLower.candidate' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms OptimalOTS.Challenge.DisclosureLower.candidate
