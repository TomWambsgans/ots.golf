import Submissions.RiscvUpper.DecodedInput
import Submissions.RiscvUpper.ExecutionContext

/-! The decoded raw inputs establish the reconstruction context. -/

namespace OptimalOTS.RiscvUpperProgram

open RiscvZkvm.Rv64

theorem decodedInput_context (image : Riscv.Image) (pk : PublicKey paperParams)
    (m : Message paperParams) (bits : List Bool) (answer : BitVec 256)
    (hdata : image.data = tableData) (hi : (answer.setWidth 128).toNat < 2 ^ 115) :
    Direct.ExecutionContext (decodedInput image pk m bits answer)
      ⟨_, hi⟩ (bits.drop 256) pk :=
  ⟨decodedInput_base image pk m bits answer hdata hi,
    decodedInput_positions image pk m bits answer hdata hi,
    decodedInput_payload image pk m bits answer hdata hi,
    decodedInput_publicKey image pk m bits answer hdata hi⟩

/-- The checked assembly decoder enters the reconstruction continuation in bounded time. -/
theorem decodePositions_continuation (image : Riscv.Image) (pk : PublicKey paperParams)
    (m : Message paperParams) (bits : List Bool) (answer : BitVec 256)
    (hdata : image.data = tableData) (hi : (answer.setWidth 128).toNat < 2 ^ 115)
    (rest fuel : ℕ) (q : OracleComp (Spec paperParams) (Option Bool))
    (located : Riscv.CodeAt
      (checkedIndexState (Riscv.writeHash (indexInputState image pk m bits) answer))
      (checkedIndexState (Riscv.writeHash (indexInputState image pk m bits) answer)).pc decodePositions)
    (bound : decodePositions.length + rest ≤ fuel)
    (continuation : ∀ left, rest ≤ left →
      Riscv.observe left (decodedInput image pk m bits answer) = q) :
    Riscv.observe fuel
      (checkedIndexState (Riscv.writeHash (indexInputState image pk m bits) answer)) = q := by
  apply PureBlock.observe_continuation decoderBlock _
    (decoderBlock_correct _ ⟨_, hi⟩ (checkedIndexState_hash_rank image pk m bits answer)
      (checkedInput_table image pk m bits answer hdata)).1
    (by simpa only [decoderBlock_code] using located) rest fuel q
    (by simpa only [decoderBlock_code] using bound)
  exact continuation

end OptimalOTS.RiscvUpperProgram
