import Submissions.RiscvUpper.Candidate

/-! A fixed-layout forest OTS with an equivalent RV64IM verifier, at 1632 accepting cycles. -/

namespace OptimalOTS.Challenge.RiscvUpper

/-- The OTS algorithms, fixed machine image, and termination witness. -/
noncomputable def submission : Riscv.Submission := RiscvUpperForest.submission

/-- Correctness, signing availability, resource limits, 127-bit strong security, exact machine
refinement on every input, and at most 1632 cycles on every accepting path. -/
theorem certificate : submission.Certificate 1632 := RiscvUpperForest.machineCertificate

end OptimalOTS.Challenge.RiscvUpper
