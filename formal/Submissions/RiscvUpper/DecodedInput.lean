import Submissions.RiscvUpper.InitialStorage
import Submissions.RiscvUpper.IndexChecks
import Submissions.RiscvUpper.NodeProgramProof

/-! The index decoder establishes the memory representation used by reconstruction. -/

namespace OptimalOTS.RiscvUpperProgram

open RiscvZkvm.Rv64

def decodedInput (image : Riscv.Image) (pk : PublicKey paperParams) (m : Message paperParams)
    (bits : List Bool) (answer : BitVec 256) : MachineState :=
  decoderBlock.eval (checkedIndexState (Riscv.writeHash (indexInputState image pk m bits) answer))

theorem checkedInput_pc (image : Riscv.Image) (pk : PublicKey paperParams)
    (m : Message paperParams) (bits : List Bool) (answer : BitVec 256) :
    (checkedIndexState (Riscv.writeHash (indexInputState image pk m bits) answer)).pc =
      Riscv.codeBase + 168 := by
  rw [checkedIndexState_pc _ (by rfl)]
  change ((indexInputState image pk m bits).pc + 4) + 56 = _
  rw [indexInput_pc]
  decide +kernel

theorem checkedInput_code (image : Riscv.Image) (pk : PublicKey paperParams)
    (m : Message paperParams) (bits : List Bool) (answer : BitVec 256) :
    (checkedIndexState (Riscv.writeHash (indexInputState image pk m bits) answer)).code =
      (Riscv.initialState image pk m bits).code := by
  rw [checkedIndexState_code]
  simp only [Riscv.writeHash, MachineState.code_setPC, MachineState.code_writeWords]
  exact Riscv.fold_code _ _

theorem checkedInput_table (image : Riscv.Image) (pk : PublicKey paperParams)
    (m : Message paperParams) (bits : List Bool) (answer : BitVec 256)
    (hdata : image.data = tableData) :
    TableLoaded (checkedIndexState (Riscv.writeHash (indexInputState image pk m bits) answer)) :=
  (indexHash_table image pk m bits hdata answer).of_mem_eq (checkedIndexState_mem _)

theorem decodedInput_code (image : Riscv.Image) (pk : PublicKey paperParams)
    (m : Message paperParams) (bits : List Bool) (answer : BitVec 256) :
    (decodedInput image pk m bits answer).code = (Riscv.initialState image pk m bits).code := by
  rw [decodedInput, PureBlock.eval_code, checkedInput_code]

theorem decodedInput_pc (image : Riscv.Image) (pk : PublicKey paperParams)
    (m : Message paperParams) (bits : List Bool) (answer : BitVec 256)
    (hdata : image.data = tableData) (hi : (answer.setWidth 128).toNat < 2 ^ 115) :
    (decodedInput image pk m bits answer).pc =
      Riscv.codeBase + BitVec.ofNat 64 (4 * (indexAndChecks.length + decodePositions.length)) := by
  rw [decodedInput, PureBlock.eval_pc _ _
    (decoderBlock_correct _ ⟨_, hi⟩ (checkedIndexState_hash_rank image pk m bits answer)
      (checkedInput_table image pk m bits answer hdata)).1,
    checkedInput_pc, decoderBlock_code]
  have length : indexAndChecks.length = 42 := by decide +kernel
  rw [length, Nat.mul_add, BitVec.ofNat_add, BitVec.add_assoc]
  rfl

theorem decodedInput_base (image : Riscv.Image) (pk : PublicKey paperParams)
    (m : Message paperParams) (bits : List Bool) (answer : BitVec 256)
    (hdata : image.data = tableData) (hi : (answer.setWidth 128).toNat < 2 ^ 115) :
    (decodedInput image pk m bits answer).getReg .x8 = BitVec.ofNat 64 positionsBase :=
  decoderBlock_base _ ⟨_, hi⟩ (checkedIndexState_hash_rank image pk m bits answer)
    (checkedInput_table image pk m bits answer hdata)

theorem decodedInput_positions (image : Riscv.Image) (pk : PublicKey paperParams)
    (m : Message paperParams) (bits : List Bool) (answer : BitVec 256)
    (hdata : image.data = tableData) (hi : (answer.setWidth 128).toNat < 2 ^ 115) :
    Direct.PositionMemory (decodedInput image pk m bits answer) (Forest.fixedPositions ⟨_, hi⟩) := by
  intro k hk
  rw [decodedInput_base image pk m bits answer hdata hi]
  exact decoderBlock_positions _ ⟨_, hi⟩ (checkedIndexState_hash_rank image pk m bits answer)
    (checkedInput_table image pk m bits answer hdata) ⟨k.val, hk⟩

theorem decodedInput_publicKey (image : Riscv.Image) (pk : PublicKey paperParams)
    (m : Message paperParams) (bits : List Bool) (answer : BitVec 256)
    (hdata : image.data = tableData) (hi : (answer.setWidth 128).toNat < 2 ^ 115) :
    MemBits (decodedInput image pk m bits answer) Riscv.publicKeyBase pk := by
  apply decoderBlock_memBits _ ⟨_, hi⟩ (checkedIndexState_hash_rank image pk m bits answer)
    (checkedInput_table image pk m bits answer hdata) _ _ (by decide) (by decide) (by decide)
  exact memBits_of_mem_eq (checkedIndexState_mem _)
    (indexHash_publicKey image pk m bits answer)

theorem decodedInput_payload (image : Riscv.Image) (pk : PublicKey paperParams)
    (m : Message paperParams) (bits : List Bool) (answer : BitVec 256)
    (hdata : image.data = tableData) (hi : (answer.setWidth 128).toNat < 2 ^ 115) :
    MemBits (decodedInput image pk m bits answer) (Riscv.signatureBase + 32)
      (ofBits 5248 (bits.drop 256)) := by
  apply decoderBlock_memBits _ ⟨_, hi⟩ (checkedIndexState_hash_rank image pk m bits answer)
    (checkedInput_table image pk m bits answer hdata) _ _ (by decide) (by decide) (by decide)
  apply memBits_of_mem_eq (checkedIndexState_mem _)
  exact indexHash_payload image pk m bits answer (by rw [hdata, tableData_length]; decide)

theorem decodedInput_nodes (image : Riscv.Image) (pk : PublicKey paperParams)
    (m : Message paperParams) (bits : List Bool) (answer : BitVec 256)
    (hdata : image.data = tableData) (hi : (answer.setWidth 128).toNat < 2 ^ 115) :
    Direct.NodeStorage (decodedInput image pk m bits answer) (fun _ => 0) := by
  intro n
  have hn := Direct.node_length_bound n
  have bounds := Direct.slotAddress_bounds n
  have aligned := (aligned_iff _).mp (Direct.slot_aligned n)
  have zero := indexHash_nodes_zero image pk m bits answer
    (by rw [hdata, tableData_length]; decide) n
  have framed := memBits_of_mem_eq (checkedIndexState_mem _) zero
  have final := decoderBlock_memBits _ ⟨_, hi⟩ (checkedIndexState_hash_rank image pk m bits answer)
    (checkedInput_table image pk m bits answer hdata) _ _ aligned
    (by simp only [BitVec.toNat_ofNat]; omega)
    (by right; simp only [BitVec.toNat_ofNat]; unfold positionsBase; omega) framed
  change MemBits (decodedInput image pk m bits answer) _ (0 : BitVec (Forest.graph.len n.fin))
  rw [Forest.graph_len_fin]
  exact final

end OptimalOTS.RiscvUpperProgram
