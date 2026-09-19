import Submissions.GenericLower.Proof

namespace OptimalOTS.Challenge.GenericLower

/-- Every admissible, secure algorithm under the paper limits needs at least one compression. -/
theorem candidate :
    AlgorithmVerificationLowerBound paperParams AlgorithmScheme.paperLimits (1 / 2 ^ 128) 1 := by
  apply OptimalOTS.GenericLower.paper_lowerBound_one
  norm_num

end OptimalOTS.Challenge.GenericLower

/--
info: 'OptimalOTS.Challenge.GenericLower.candidate' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms OptimalOTS.Challenge.GenericLower.candidate
