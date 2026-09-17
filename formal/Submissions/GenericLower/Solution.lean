import Submissions.GenericLower.Proof

namespace OptimalOTS.Challenge.GenericLower

/-- No admissible, weakly secure algorithm under the paper limits has a verification budget below one. -/
theorem candidate :
    AlgorithmVerificationLowerBound paperParams AlgorithmScheme.paperLimits (1 / 2) 1 :=
  OptimalOTS.GenericLower.candidate

end OptimalOTS.Challenge.GenericLower

/--
info: 'OptimalOTS.Challenge.GenericLower.candidate' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms OptimalOTS.Challenge.GenericLower.candidate
