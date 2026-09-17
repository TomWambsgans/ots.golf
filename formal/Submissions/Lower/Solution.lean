import OptimalOTS.Statement
import Submissions.Lower.Elementary

/-!
# An unconditional certificate for the bare single-oracle model

Every verification pays for the index and the root hash. This interim certificate makes no
independence assumption and does not need security. The stronger entropy argument is under review.
-/

namespace OptimalOTS

/-- Every weakly secure bare-oracle scheme has a verification costing at least two compressions. -/
theorem verificationLowerBound_paper : VerificationLowerBound paperParams 2 := by
  intro S _
  exact ⟨⟨0, by decide⟩, S.two_le_verifyCost _⟩

/-- The exported lower-track certificate. -/
theorem Challenge.Lower.candidate : VerificationLowerBound paperParams 2 :=
  verificationLowerBound_paper

end OptimalOTS
