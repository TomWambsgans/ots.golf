import Submissions.RiscvUpper.IndexChecks

/-! The complete initial query and wire-format checks, split into prefix, HASH and checks. -/

namespace OptimalOTS.RiscvUpperProgram

open RiscvZkvm.Rv64 OracleComp

theorem indexAndChecks_parts : indexAndChecks = indexPrefix ++ .ECALL :: indexChecks := by
  simp only [indexAndChecks, List.append_assoc, List.singleton_append]

end OptimalOTS.RiscvUpperProgram
