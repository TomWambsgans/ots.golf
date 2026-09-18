import Submissions.RiscvUpper.Candidate

/-! A fixed-layout forest OTS with an equivalent RV64IM verifier, at 24053 accepting cycles. -/

namespace OptimalOTS.Challenge.RiscvUpper

/-- The OTS algorithms, fixed machine image, and termination witness. -/
noncomputable def submission : Riscv.Submission := RiscvUpperForest.submission

/-- Correctness, signing availability, resource limits, 127-bit strong security, exact machine
refinement on every input, and at most 24053 cycles on every accepting path. -/
theorem certificate : submission.Certificate 24053 := RiscvUpperForest.machineCertificate

end OptimalOTS.Challenge.RiscvUpper
