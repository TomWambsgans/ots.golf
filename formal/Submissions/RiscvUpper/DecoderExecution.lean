import Submissions.RiscvUpper.DecodedInput
import Submissions.RiscvUpper.ExecutionContext

/-! The checked raw inputs establish the reconstruction context. -/

namespace OptimalOTS.RiscvUpperProgram

open RiscvZkvm.Rv64

theorem decodedInput_context (image : Riscv.Image) (pk : PublicKey paperParams)
    (m : Message paperParams) (bits : List Bool) (answer : BitVec 256)
    (hdata : image.data.length ≤ 1048576) (hi : Accepted (answer.setWidth 128).toNat) :
    Direct.ExecutionContext (decodedInput image pk m bits answer)
      (acceptedIdx answer hi) (bits.drop 128) pk :=
  ⟨decodedInput_base image pk m bits answer,
    decodedInput_positions image pk m bits answer hi,
    decodedInput_payload image pk m bits answer hdata,
    decodedInput_publicKey image pk m bits answer⟩

end OptimalOTS.RiscvUpperProgram
