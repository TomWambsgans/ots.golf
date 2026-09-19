import Submissions.RiscvUpper.InitialStorage
import Submissions.RiscvUpper.IndexChecks
import Submissions.RiscvUpper.NodeProgramProof

/-! The checked state establishes the memory representation used by reconstruction. -/

namespace OptimalOTS.RiscvUpperProgram

open RiscvZkvm.Rv64

/-- The state entering the chain phase: the index accepted and the positions written. -/
def decodedInput (image : Riscv.Image) (pk : PublicKey paperParams) (m : Message paperParams)
    (bits : List Bool) (answer : BitVec 256) : MachineState :=
  checkedIndexState (Riscv.writeHash (indexInputState image pk m bits) answer)

theorem decodedInput_pc (image : Riscv.Image) (pk : PublicKey paperParams)
    (m : Message paperParams) (bits : List Bool) (answer : BitVec 256) :
    (decodedInput image pk m bits answer).pc =
      Riscv.codeBase + BitVec.ofNat 64 (4 * indexAndChecks.length) := by
  rw [decodedInput, checkedIndexState_pc _ (by rfl)]
  change ((indexInputState image pk m bits).pc + 4) + 996 = _
  rw [indexInput_pc, indexAndChecks_length]
  decide +kernel

theorem decodedInput_code (image : Riscv.Image) (pk : PublicKey paperParams)
    (m : Message paperParams) (bits : List Bool) (answer : BitVec 256) :
    (decodedInput image pk m bits answer).code = (Riscv.initialState image pk m bits).code := by
  rw [decodedInput, checkedIndexState_code]
  simp only [Riscv.writeHash, MachineState.code_setPC, MachineState.code_writeWords]
  exact Riscv.fold_code _ _

theorem decodedInput_base (image : Riscv.Image) (pk : PublicKey paperParams)
    (m : Message paperParams) (bits : List Bool) (answer : BitVec 256) :
    (decodedInput image pk m bits answer).getReg .x8 = BitVec.ofNat 64 positionsBase :=
  checkedIndexState_base _

theorem decodedInput_rank (image : Riscv.Image) (pk : PublicKey paperParams)
    (m : Message paperParams) (bits : List Bool) (answer : BitVec 256) :
    rankOf (decodedInput image pk m bits answer) = (answer.setWidth 128).toNat :=
  checkedIndexState_hash_rank image pk m bits answer

/-- The stored positions are exactly the layout's chain positions for the accepted index. -/
theorem decodedInput_positions (image : Riscv.Image) (pk : PublicKey paperParams)
    (m : Message paperParams) (bits : List Bool) (answer : BitVec 256)
    (hi : Accepted (answer.setWidth 128).toNat) :
    Direct.PositionMemory (decodedInput image pk m bits answer)
      (Forest.fixedPositions (acceptedIdx answer hi)) := by
  intro k hk
  rw [decodedInput_base]
  have pos := checked_position (Riscv.writeHash (indexInputState image pk m bits) answer) k.val hk
  rw [indexOf_hash] at pos
  change (checkedIndexState (Riscv.writeHash (indexInputState image pk m bits) answer)).getMem
    (positionAddr k.val) = _
  rw [pos]
  unfold Forest.fixedPositions
  rw [dif_pos hk, Fin.val_rev, Forest.fixedDigits_val, Forest.digitAt]
  simp only [Fin.val_mk]
  by_cases h32 : k.val < 32
  · rw [if_pos h32, if_pos h32]
    have le := Forest.nibble_le (acceptedIdx answer hi) k.val h32
    rw [acceptedIdx_val] at le
    have e := BitVec.ofNat_sub_ofNat_of_le (w := 64) 14 (nibble (answer.setWidth 128).toNat k.val)
      (by have := nibble_lt (answer.setWidth 128).toNat k.val; omega) le
    rw [acceptedIdx_val]
    refine Eq.trans ?_ (e.trans (congrArg _ (by omega)))
    rfl
  · rw [if_neg h32, if_neg h32]
    rfl

theorem decodedInput_publicKey (image : Riscv.Image) (pk : PublicKey paperParams)
    (m : Message paperParams) (bits : List Bool) (answer : BitVec 256) :
    MemBits (decodedInput image pk m bits answer) Riscv.publicKeyBase pk := by
  apply checked_memBits _ _ _ (by decide) (by decide) (by decide)
  exact indexHash_publicKey image pk m bits answer

theorem decodedInput_payload (image : Riscv.Image) (pk : PublicKey paperParams)
    (m : Message paperParams) (bits : List Bool) (answer : BitVec 256)
    (hdata : image.data.length ≤ 1048576) :
    MemBits (decodedInput image pk m bits answer) (Riscv.signatureBase + 16)
      (ofBits 5248 (bits.drop 128)) := by
  apply checked_memBits _ _ _ (by decide) (by decide) (by decide)
  exact indexHash_payload image pk m bits answer hdata

theorem decodedInput_nodes (image : Riscv.Image) (pk : PublicKey paperParams)
    (m : Message paperParams) (bits : List Bool) (answer : BitVec 256)
    (hdata : image.data.length ≤ 1048576) :
    Direct.NodeStorage (decodedInput image pk m bits answer) (fun _ => 0) := by
  intro n
  have hn := Direct.node_length_bound n
  have bounds := Direct.slotAddress_bounds n
  have aligned := (aligned_iff _).mp (Direct.slot_aligned n)
  have zero := indexHash_nodes_zero image pk m bits answer hdata n
  have final := checked_memBits _ _ _ aligned
    (by simp only [BitVec.toNat_ofNat]; omega)
    (by right; simp only [BitVec.toNat_ofNat]; unfold positionsBase; omega) zero
  change MemBits (decodedInput image pk m bits answer) _ (0 : BitVec (Forest.graph.len n.fin))
  rw [Forest.graph_len_fin]
  exact final

end OptimalOTS.RiscvUpperProgram
