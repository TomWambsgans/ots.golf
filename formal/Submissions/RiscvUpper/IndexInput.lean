import Submissions.RiscvUpper.CopyProof

/-! The ordinary-instruction prefix preparing the verifier's first oracle query. -/

namespace OptimalOTS.RiscvUpperProgram

open RiscvZkvm.Rv64


def indexInputState (image : Riscv.Image) (pk : PublicKey paperParams)
    (m : Message paperParams) (bits : List Bool) : MachineState :=
  indexPrefix.foldl execInstrBr (Riscv.initialState image pk m bits)

theorem indexPrefix_length : indexPrefix.length = 23 := by decide +kernel

theorem indexPrefix_ready (image : Riscv.Image) (pk : PublicKey paperParams)
    (m : Message paperParams) (bits : List Bool) :
    Riscv.LinearReady (Riscv.initialState image pk m bits) indexPrefix := by
  simp [indexPrefix, constant, copy128, Riscv.LinearReady, Riscv.linearInstruction,
    Riscv.memoryReady, execInstrBr, Riscv.initialState, MachineState.getReg, MachineState.setReg,
    MachineState.setMem, MachineState.setPC, scratchBase, Riscv.signatureBase,
    Riscv.messageBase, signExtend12, MachineState.getMem, MEM_START, MEM_END]

theorem indexInput_registers (image : Riscv.Image) (pk : PublicKey paperParams)
    (m : Message paperParams) (bits : List Bool) :
    let s := indexInputState image pk m bits
    s.getReg .x5 = 1 ∧ s.getReg .x10 = BitVec.ofNat 64 scratchBase ∧
    s.getReg .x11 = 384 ∧ s.getReg .x12 = BitVec.ofNat 64 (scratchBase + 128) ∧
    s.getReg .x13 = BitVec.ofNat 64 (min bits.length 5377) := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The first half of the input is the nonce; the second is the message. -/
theorem indexInput_word (image : Riscv.Image) (pk : PublicKey paperParams)
    (m : Message paperParams) (bits : List Bool) (j : Fin 6) :
    (indexInputState image pk m bits).getMem (BitVec.ofNat 64 (scratchBase + 8 * j.val)) =
      if j.val < 2 then
        (Riscv.initialState image pk m bits).getMem
          (Riscv.signatureBase + BitVec.ofNat 64 (8 * j.val))
      else (Riscv.initialState image pk m bits).getMem
          (Riscv.messageBase + BitVec.ofNat 64 (8 * (j.val - 2))) := by
  fin_cases j <;> rfl

set_option maxRecDepth 100000 in
/-- The prepared HASH input is exactly the specification's message/nonce concatenation. -/
theorem indexInput_memBits (image : Riscv.Image) (pk : PublicKey paperParams)
    (m : Message paperParams) (bits : List Bool) (hdata : image.data.length ≤ 1048576) :
    MemBits (indexInputState image pk m bits) (BitVec.ofNat 64 scratchBase)
      (m ++ ofBits 128 bits) := by
  apply memBits_of_words _ _ _ (by decide +kernel)
  intro j hj
  change j < 6 at hj
  rw [← BitVec.ofNat_add, indexInput_word image pk m bits ⟨j, hj⟩]
  by_cases hlow : j < 2
  · rw [if_pos hlow, initialState_signature_word image pk m bits hdata j (by omega),
      BitVec.extractLsb'_append_eq_of_add_le (by omega), ofBits_extract _ (by omega),
      ofBits_drop_take _ (by omega)]
  · rw [if_neg hlow, initialState_message_word image pk m bits (j - 2) (by omega),
      BitVec.extractLsb'_append_eq_of_le (by omega)]
    congr 1
    omega

/-- The first query includes all 384 input bits and uses the prescribed scratch output. -/
theorem indexInput_hash (image : Riscv.Image) (pk : PublicKey paperParams)
    (m : Message paperParams) (bits : List Bool) (hdata : image.data.length ≤ 1048576) :
    Riscv.hashInput (indexInputState image pk m bits) = ⟨384, m ++ ofBits 128 bits⟩ := by
  have hr := indexInput_registers image pk m bits
  apply hashInput_of_memBits hr.2.1 _ (indexInput_memBits image pk m bits hdata)
  rw [hr.2.2.1]
  rfl

theorem indexInput_hashValid (image : Riscv.Image) (pk : PublicKey paperParams)
    (m : Message paperParams) (bits : List Bool) :
    Riscv.hashArgumentsValid (indexInputState image pk m bits) = true := by
  have hr := indexInput_registers image pk m bits
  unfold Riscv.hashArgumentsValid
  rw [hr.2.1, hr.2.2.1, hr.2.2.2.1]
  decide +kernel

theorem indexInput_pc (image : Riscv.Image) (pk : PublicKey paperParams)
    (m : Message paperParams) (bits : List Bool) :
    (indexInputState image pk m bits).pc = Riscv.codeBase + 92 := by
  rw [indexInputState, Riscv.linear_fold_pc _ _ (indexPrefix_ready image pk m bits), indexPrefix_length]
  have h : (Riscv.initialState image pk m bits).pc = Riscv.codeBase := by
    simp [Riscv.initialState]
  rw [h]
  rfl

set_option maxHeartbeats 3000000 in
/-- Preparing the query copies precisely six words into scratch memory. -/
theorem indexInput_mem (image : Riscv.Image) (pk : PublicKey paperParams)
    (m : Message paperParams) (bits : List Bool) :
    let initial := Riscv.initialState image pk m bits
    (indexInputState image pk m bits).mem =
      (initial.writeWords (BitVec.ofNat 64 scratchBase)
        [initial.getMem (Riscv.signatureBase + 0), initial.getMem (Riscv.signatureBase + 8),
         initial.getMem (Riscv.messageBase + 0), initial.getMem (Riscv.messageBase + 8),
         initial.getMem (Riscv.messageBase + 16), initial.getMem (Riscv.messageBase + 24)]).mem := by
  rfl

/-- Preparing the query changes only its six scratch doublewords. -/
theorem indexInput_frame (image : Riscv.Image) (pk : PublicKey paperParams)
    (m : Message paperParams) (bits : List Bool) (addr : Word)
    (h : ∀ j : Fin 6, addr ≠ BitVec.ofNat 64 (scratchBase + 8 * j.val)) :
    (indexInputState image pk m bits).getMem addr =
      (Riscv.initialState image pk m bits).getMem addr := by
  have heq := congrFun (indexInput_mem image pk m bits) addr
  change (indexInputState image pk m bits).getMem addr =
    (MachineState.writeWords _ _ _).getMem addr at heq
  rw [heq, getMem_writeWords_of_disjoint]
  intro j hj
  simpa only [BitVec.ofNat_add] using h ⟨j, hj⟩

/-- Every address outside the scratch input interval retains its loaded value. -/
theorem indexInput_frame_interval (image : Riscv.Image) (pk : PublicKey paperParams)
    (m : Message paperParams) (bits : List Bool) (addr : Word)
    (h : addr.toNat < scratchBase ∨ scratchBase + 48 ≤ addr.toNat) :
    (indexInputState image pk m bits).getMem addr =
      (Riscv.initialState image pk m bits).getMem addr := by
  apply indexInput_frame
  intro j heq
  have hi := j.isLt
  have ha := congrArg BitVec.toNat heq
  simp only [BitVec.toNat_ofNat] at ha
  unfold scratchBase at h ha
  omega

end OptimalOTS.RiscvUpperProgram
