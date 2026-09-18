import OptimalOTS.Riscv
import Submissions.RiscvUpper.Wire
import Submissions.RiscvUpper.DirectCost

/-! The proved OTS specification and its direct RV64IM implementation. -/

namespace OptimalOTS.RiscvUpperForest

noncomputable def submission : Riscv.Submission where
  SecretKey := Wire.scheme.SecretKey
  keygen := Wire.scheme.keygen
  sign := Wire.scheme.sign
  verify := Wire.scheme.verify
  image := RiscvUpperProgram.Direct.image
  fuel := fun _ _ _ => 114557

theorem submission_scheme : submission.scheme = Wire.scheme := rfl

theorem submission_admissible :
    submission.scheme.Admissible AlgorithmScheme.paperLimits (1 / 2 ^ 128) := by
  rw [submission_scheme]
  exact Wire.admissible

theorem submission_secure : submission.scheme.Secure := by
  rw [submission_scheme]
  exact Wire.secure

/-- The accepting-cycle obligation is independent of implementation refinement. -/
theorem submission_cost : submission.AcceptCostAtMost 229113 := by
  intro pk m bits cycles accepted
  exact RiscvUpperProgram.Direct.execution_cost pk m bits true cycles accepted

end OptimalOTS.RiscvUpperForest
