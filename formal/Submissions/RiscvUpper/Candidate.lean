import OptimalOTS.Riscv
import Submissions.RiscvUpper.Wire
import Submissions.RiscvUpper.CompactVerifier

/-! The proved OTS specification and its compact RV64IM implementation. -/

namespace OptimalOTS.RiscvUpperForest

open OracleComp

noncomputable def submission : Riscv.Submission where
  SecretKey := Wire.scheme.SecretKey
  keygen := Wire.scheme.keygen
  sign := Wire.scheme.sign
  verify := Wire.scheme.verify
  image := RiscvUpperProgram.Compact.image
  fuel := fun _ _ _ => 24058

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
  refine ⟨RiscvUpperProgram.Compact.image_valid, fun pk m bits => ?_⟩
  change Riscv.observe 24058 (Riscv.initialState RiscvUpperProgram.Compact.image pk m bits) =
    some <$> Wire.scheme.verify pk m bits
  rw [(RiscvUpperProgram.Compact.image_refines pk m bits).1, ForestVerifier.directVerify_eq]

/-- Every accepting run executes at most 19627 cycles: one per executed instruction, two for
the 912-bit root hash, with the decoder charged as straight-line code. -/
theorem submission_cost : submission.AcceptCostAtMost 19627 := by
  intro pk m bits cycles accepted
  exact (RiscvUpperProgram.Compact.image_refines pk m bits).2 true cycles accepted

/-- Every requirement of a scored RISC-V submission, at 19627 cycles. -/
theorem machineCertificate : submission.Certificate 19627 :=
  ⟨submission_admissible, submission_secure, submission_implements, submission_cost⟩

/--
info: 'OptimalOTS.RiscvUpperForest.machineCertificate' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms machineCertificate

end OptimalOTS.RiscvUpperForest
