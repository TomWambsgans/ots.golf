import OptimalOTS.Riscv
import Submissions.RiscvUpper.Wire
import Submissions.RiscvUpper.DirectCost
import Submissions.RiscvUpper.VerifierProof

/-! The proved OTS specification and its direct RV64IM implementation. -/

namespace OptimalOTS.RiscvUpperForest

open OracleComp

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

/-- The machine's complete oracle computation is the certified verifier on every input, so
every execution terminates within the fixed fuel and issues exactly the specified queries. -/
theorem submission_implements : submission.Implements := by
  refine ⟨RiscvUpperProgram.Direct.image_valid, fun pk m bits => ?_⟩
  change Riscv.observe 114557 (Riscv.initialState RiscvUpperProgram.Direct.image pk m bits) =
    some <$> Wire.scheme.verify pk m bits
  rw [RiscvUpperProgram.Direct.image_observe pk m bits 114557 le_rfl,
    ForestVerifier.directVerify_eq]

/-- The accepting-cycle obligation is independent of implementation refinement. -/
theorem submission_cost : submission.AcceptCostAtMost 229113 := by
  intro pk m bits cycles accepted
  exact RiscvUpperProgram.Direct.execution_cost pk m bits true cycles accepted

/-- Every requirement of a scored RISC-V submission, at 229113 virtual cycles. -/
theorem machineCertificate : submission.Certificate 229113 :=
  ⟨submission_admissible, submission_secure, submission_implements, submission_cost⟩

/--
info: 'OptimalOTS.RiscvUpperForest.machineCertificate' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms machineCertificate

end OptimalOTS.RiscvUpperForest
