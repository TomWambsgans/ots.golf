import Submissions.RiscvUpper.IndexInput
import Submissions.RiscvUpper.HashOutput
import Submissions.RiscvUpper.DecoderProof

/-! The verifier's post-HASH index and signature-length checks. -/

namespace OptimalOTS.RiscvUpperProgram

open RiscvZkvm.Rv64

set_option maxRecDepth 100000

def indexLoads : Code := [.LD .x20 .x19 128, .LD .x21 .x19 136, .SRLI .x26 .x21 51]

def indexLengthCheck : Code := constant .x26 5504 ++ [.XOR .x26 .x26 .x13]

def indexChecks : Code :=
  indexLoads ++ whenNonzero .x26 reject ++ indexLengthCheck ++ whenNonzero .x26 reject

theorem indexAndChecks_split : indexAndChecks = indexPrefix ++ [.ECALL] ++ indexChecks := by
  decide +kernel

theorem indexChecks_length : indexChecks.length = 14 := by decide +kernel

def skipReject (s : MachineState) : MachineState := s.setPC (s.pc + 16)

def checkedIndexState (s : MachineState) : MachineState :=
  skipReject (indexLengthCheck.foldl execInstrBr
    (skipReject (indexLoads.foldl execInstrBr s)))

theorem indexLoads_ready (s : MachineState)
    (scratch : s.getReg .x19 = BitVec.ofNat 64 scratchBase) :
    Riscv.LinearReady s indexLoads := by
  simp [indexLoads, Riscv.LinearReady, Riscv.linearInstruction, Riscv.memoryReady,
    execInstrBr, scratch, MachineState.getReg_setReg_ne, scratchBase,
    signExtend12, MEM_START, MEM_END]

theorem indexLengthCheck_ready (s : MachineState) : Riscv.LinearReady s indexLengthCheck := by
  simp [indexLengthCheck, constant, Riscv.LinearReady, Riscv.linearInstruction, Riscv.memoryReady]

theorem reject_observe (s : MachineState) (fuel : ℕ)
    (located : Riscv.CodeAt s s.pc reject) (bound : 3 ≤ fuel) :
    Riscv.observe fuel s = pure (some false) := by
  let front : Code := [.ADDI .x5 .x0 0, .ADDI .x10 .x0 0]
  have ready : Riscv.LinearReady s front := by
    simp [front, Riscv.LinearReady, Riscv.linearInstruction, Riscv.memoryReady]
  have code : Riscv.CodeAt s s.pc (front ++ [.ECALL]) := located
  have h := Riscv.observe_linear (fuel - 2) s front code.append_left ready
  have pc : (front.foldl execInstrBr s).pc = s.pc + 8 := by
    simpa [front] using Riscv.linear_fold_pc s front ready
  have halt : Riscv.CodeAt (front.foldl execInstrBr s)
      (front.foldl execInstrBr s).pc [.ECALL] := by
    rw [pc]
    exact code.append_right.code_eq (Riscv.fold_code s front)
  have total : front.length + (fuel - 2) = fuel := by simp [front]; omega
  rw [total] at h
  rw [h, show fuel - 2 = (fuel - 3) + 1 by omega]
  exact Riscv.observe_halt _ _ false halt.head rfl rfl

/-- A failed check reaches HALT false; a passed check jumps over that complete block. -/
theorem checkedBranch_observe (s : MachineState) (fuel : ℕ)
    (located : Riscv.CodeAt s s.pc (whenNonzero .x26 reject)) (bound : 4 ≤ fuel) :
    Riscv.observe fuel s =
      if s.getReg .x26 = 0#64 then Riscv.observe (fuel - 1) (skipReject s)
      else pure (some false) := by
  have branch := whenNonzero_observe (fuel - 1) s .x26 reject (by decide) located
  rw [show fuel - 1 + 1 = fuel by omega] at branch
  change Riscv.observe fuel s = Riscv.observe (fuel - 1)
    (s.setPC (s.pc + if s.getReg .x26 = 0#64 then 16 else 4)) at branch
  rw [branch]
  split_ifs with h
  · rfl
  · apply reject_observe _ _ _ (by omega)
    exact located.tail.code_eq rfl

theorem checkedIndexState_pc (s : MachineState)
    (scratch : s.getReg .x19 = BitVec.ofNat 64 scratchBase) :
    (checkedIndexState s).pc = s.pc + 56 := by
  simp only [checkedIndexState, skipReject, MachineState.setPC]
  rw [Riscv.linear_fold_pc _ _ (indexLengthCheck_ready _),
    Riscv.linear_fold_pc _ _ (indexLoads_ready s scratch)]
  change (((s.pc + 12) + 16) + 12) + 16 = s.pc + 56
  simp only [BitVec.add_assoc]
  rfl

theorem checkedIndexState_code (s : MachineState) : (checkedIndexState s).code = s.code := by
  simp only [checkedIndexState, skipReject, MachineState.code_setPC, Riscv.fold_code]

theorem checkedIndexState_mem (s : MachineState) : (checkedIndexState s).mem = s.mem := rfl

theorem indexLoads_registers (s : MachineState) :
    let t := indexLoads.foldl execInstrBr s
    t.getReg .x20 = s.getMem (s.getReg .x19 + 128) ∧
    t.getReg .x21 = s.getMem (s.getReg .x19 + 136) ∧
    t.getReg .x26 = s.getMem (s.getReg .x19 + 136) >>> 51 ∧
    t.getReg .x13 = s.getReg .x13 := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem indexLengthCheck_test (s : MachineState) :
    (indexLengthCheck.foldl execInstrBr s).getReg .x26 = 5504 ^^^ s.getReg .x13 := rfl

theorem checkedIndexState_rank (s : MachineState) :
    rankOf (checkedIndexState s) =
      (joinWords (s.getMem (s.getReg .x19 + 128))
        (s.getMem (s.getReg .x19 + 136))).toNat := rfl

theorem answer_low128 (answer : BitVec 256) :
    joinWords (answer.extractLsb' 0 64) (answer.extractLsb' 64 64) =
      answer.setWidth 128 := by
  rw [joinWords, BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by decide)]
  ext i hi
  simp

theorem highWord_shift_zero (lo hi : Word) :
    hi >>> 51 = 0#64 ↔ (joinWords lo hi).toNat < 2 ^ 115 := by
  rw [← BitVec.toNat_inj, BitVec.toNat_ushiftRight, BitVec.toNat_zero,
    Nat.shiftRight_eq_div_pow, Nat.div_eq_zero_iff, joinWords_toNat]
  have := lo.isLt
  constructor <;> intro h <;> omega

theorem capped_length_eq (bits : List Bool) :
    (5504 : Word) ^^^ BitVec.ofNat 64 (min bits.length 5505) = 0#64 ↔ bits.length = 5504 := by
  rw [BitVec.xor_eq_zero_iff]
  constructor
  · intro h
    have hn := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat] at hn
    have bound : min bits.length 5505 < 2 ^ 64 := by omega
    rw [Nat.mod_eq_of_lt bound] at hn
    change 5504 = min bits.length 5505 at hn
    omega
  · intro h
    simp [h]

/-- The suffix either rejects or reaches its continuation in eight instructions. -/
theorem indexChecks_observe (s : MachineState) (fuel : ℕ)
    (scratch : s.getReg .x19 = BitVec.ofNat 64 scratchBase)
    (located : Riscv.CodeAt s s.pc indexChecks) (bound : 14 ≤ fuel) :
    Riscv.observe fuel s =
      if s.getMem (s.getReg .x19 + 136) >>> 51 = 0#64 ∧
          (5504 : Word) ^^^ s.getReg .x13 = 0#64 then
        Riscv.observe (fuel - 8) (checkedIndexState s)
      else pure (some false) := by
  let a := indexLoads.foldl execInstrBr s
  let b := skipReject a
  let c := indexLengthCheck.foldl execInstrBr b
  have code : Riscv.CodeAt s s.pc
      (indexLoads ++ (whenNonzero .x26 reject ++
        (indexLengthCheck ++ whenNonzero .x26 reject))) := by
    simpa only [indexChecks, List.append_assoc] using located
  have aPC : a.pc = s.pc + BitVec.ofNat 64 (4 * indexLoads.length) :=
    Riscv.linear_fold_pc s _ (indexLoads_ready s scratch)
  have aCode : Riscv.CodeAt a a.pc (whenNonzero .x26 reject ++
      (indexLengthCheck ++ whenNonzero .x26 reject)) := by
    rw [aPC]
    exact code.append_right.code_eq (Riscv.fold_code s indexLoads)
  have bCode : Riscv.CodeAt b b.pc (indexLengthCheck ++ whenNonzero .x26 reject) :=
    aCode.append_right.code_eq rfl
  have cPC : c.pc = b.pc + BitVec.ofNat 64 (4 * indexLengthCheck.length) :=
    Riscv.linear_fold_pc b _ (indexLengthCheck_ready b)
  have cCode : Riscv.CodeAt c c.pc (whenNonzero .x26 reject) := by
    rw [cPC]
    exact bCode.append_right.code_eq (Riscv.fold_code b indexLengthCheck)
  have loadRun := Riscv.observe_linear (fuel - 3) s indexLoads code.append_left
    (indexLoads_ready s scratch)
  rw [show indexLoads.length + (fuel - 3) = fuel by
    change 3 + (fuel - 3) = fuel; omega] at loadRun
  rw [loadRun, checkedBranch_observe a (fuel - 3) aCode.append_left (by omega)]
  have aTest : a.getReg .x26 = s.getMem (s.getReg .x19 + 136) >>> 51 :=
    (indexLoads_registers s).2.2.1
  have cTest : c.getReg .x26 = (5504 : Word) ^^^ s.getReg .x13 := rfl
  rw [aTest]
  by_cases first : s.getMem (s.getReg .x19 + 136) >>> 51 = 0#64
  · simp only [first, if_pos, true_and]
    have lenRun := Riscv.observe_linear (fuel - 7) b indexLengthCheck bCode.append_left
      (indexLengthCheck_ready b)
    rw [show indexLengthCheck.length + (fuel - 7) = fuel - 3 - 1 by
      change 3 + (fuel - 7) = fuel - 3 - 1; omega] at lenRun
    rw [lenRun, checkedBranch_observe c (fuel - 7) cCode (by omega), cTest]
    split_ifs with second
    · have hc : skipReject c = checkedIndexState s := rfl
      rw [hc]
      congr 1
    · rfl
  · simp only [first, false_and, ite_false]

/-- The checked state retains the actual oracle index in its two decoder registers. -/
theorem checkedIndexState_hash_rank (image : Riscv.Image) (pk : PublicKey paperParams)
    (m : Message paperParams) (bits : List Bool) (answer : BitVec 256) :
    rankOf (checkedIndexState (Riscv.writeHash (indexInputState image pk m bits) answer)) =
      (answer.setWidth 128).toNat := by
  rw [checkedIndexState_rank]
  have low := writeHash_word (indexInputState image pk m bits) answer 0 (by decide)
  have high := writeHash_word (indexInputState image pk m bits) answer 1 (by decide)
  change (Riscv.writeHash (indexInputState image pk m bits) answer).getMem
    (BitVec.ofNat 64 (scratchBase + 128)) = answer.extractLsb' 0 64 at low
  change (Riscv.writeHash (indexInputState image pk m bits) answer).getMem
    (BitVec.ofNat 64 (scratchBase + 136)) = answer.extractLsb' 64 64 at high
  change (joinWords
    ((Riscv.writeHash (indexInputState image pk m bits) answer).getMem
      (BitVec.ofNat 64 (scratchBase + 128)))
    ((Riscv.writeHash (indexInputState image pk m bits) answer).getMem
      (BitVec.ofNat 64 (scratchBase + 136)))).toNat = _
  rw [low, high, answer_low128]

/-- Both wire-format checks are exact, and any proved continuation can follow them. -/
theorem indexChecks_continuation (image : Riscv.Image) (pk : PublicKey paperParams)
    (m : Message paperParams) (bits : List Bool) (answer : BitVec 256)
    (rest fuel : ℕ) (q : OracleComp (Spec paperParams) (Option Bool))
    (located : Riscv.CodeAt (Riscv.writeHash (indexInputState image pk m bits) answer)
      (Riscv.writeHash (indexInputState image pk m bits) answer).pc indexChecks)
    (bound : indexChecks.length + rest ≤ fuel)
    (continuation : (answer.setWidth 128).toNat < 2 ^ 115 → bits.length = 5504 →
      ∀ left, rest ≤ left →
        Riscv.observe left
          (checkedIndexState (Riscv.writeHash (indexInputState image pk m bits) answer)) = q) :
    Riscv.observe fuel (Riscv.writeHash (indexInputState image pk m bits) answer) =
      if (answer.setWidth 128).toNat < 2 ^ 115 ∧ bits.length = 5504 then q
      else pure (some false) := by
  let s := Riscv.writeHash (indexInputState image pk m bits) answer
  have scratch : s.getReg .x19 = BitVec.ofNat 64 scratchBase := rfl
  have size : s.getReg .x13 = BitVec.ofNat 64 (min bits.length 5505) := rfl
  have high := writeHash_word (indexInputState image pk m bits) answer 1 (by decide)
  change s.getMem (s.getReg .x19 + 136) = answer.extractLsb' 64 64 at high
  have fit : answer.extractLsb' 64 64 >>> 51 = 0#64 ↔
      (answer.setWidth 128).toNat < 2 ^ 115 := by
    rw [highWord_shift_zero (answer.extractLsb' 0 64), answer_low128]
  rw [indexChecks_observe s fuel scratch located (by rw [indexChecks_length] at bound; omega),
    high, size]
  simp only [fit, capped_length_eq]
  split_ifs with passed
  · exact continuation passed.1 passed.2 _ (by rw [indexChecks_length] at bound; omega)
  · rfl

/-- The completed decoder retains the base pointer used to read its decoded positions. -/
theorem decoderBlock_base (s : MachineState) (index : Fin (2 ^ 115))
    (rankEq : rankOf s = index.val) (table : TableLoaded s) :
    (decoderBlock.eval s).getReg .x8 = BitVec.ofNat 64 positionsBase := by
  let initCode := constant .x8 positionsBase ++ constant .x22 121
  let start := initCode.foldl execInstrBr s
  have baseLiteral : literalValue positionsBase = BitVec.ofNat 64 positionsBase := by decide +kernel
  have startReg (r : Reg) (h8 : r ≠ .x8) (h22 : r ≠ .x22) :
      start.getReg r = s.getReg r := by
    simp [start, initCode, List.foldl_append, constant_preserves, Ne.symm h8, Ne.symm h22]
  have startSum : start.getReg .x22 = BitVec.ofNat 64 121 := by
    simp [start, initCode, List.foldl_append, constant_value,
      literalValue_small _ (by decide : 121 < 2048)]
  have startBase : start.getReg .x8 = BitVec.ofNat 64 positionsBase := by
    simp [start, initCode, List.foldl_append, constant_value, constant_preserves, baseLiteral]
  have startMem : start.mem = s.mem := by
    simp only [start, initCode, List.foldl_append, constant_mem]
  have startRank : rankOf start = index.val := by
    simpa only [rankOf, startReg .x20 (by decide) (by decide),
      startReg .x21 (by decide) (by decide)] using rankEq
  have result := decodeBlock_correct start 36 0 121 (by decide) le_rfl startSum startBase
    (table.of_mem_eq startMem)
    (by rw [startRank]; exact index.isLt.trans_le Forest.fixed_count)
  unfold decoderBlock
  rw [PureBlock.eval]
  exact result.2.1

end OptimalOTS.RiscvUpperProgram
