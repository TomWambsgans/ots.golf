import Submissions.RiscvUpper.BlockExecution
import Submissions.RiscvUpper.Program

/-! Verified ordinary-instruction macros used by the assembly proof. -/

namespace OptimalOTS.RiscvUpperProgram

open RiscvZkvm.Rv64

/-- The literal word computed by the assembler's one- or two-instruction expansion. -/
def literalValue (n : ℕ) : Word :=
  if n < 2048 then signExtend12 (BitVec.ofNat 12 n) else
    ((BitVec.ofNat 20 ((n + 2048) / 4096)).zeroExtend 32 <<< 12).signExtend 64 +
      signExtend12 (BitVec.ofNat 12 n)

theorem constant_ready (s : MachineState) (r : Reg) (n : ℕ) :
    Riscv.LinearReady s (constant r n) := by
  unfold constant
  split <;> simp [Riscv.LinearReady, Riscv.linearInstruction, Riscv.memoryReady]

theorem constant_value (s : MachineState) (r : Reg) (n : ℕ) (nonzero : r ≠ .x0) :
    ((constant r n).foldl execInstrBr s).getReg r = literalValue n := by
  unfold constant literalValue
  split <;> simp only [List.foldl_cons, List.foldl_nil, execInstrBr,
    MachineState.getReg_setPC, MachineState.getReg_setReg_eq nonzero,
    show s.getReg .x0 = 0 from rfl]
  exact BitVec.zero_add _

theorem constant_preserves (s : MachineState) (r other : Reg) (n : ℕ) (different : r ≠ other) :
    ((constant r n).foldl execInstrBr s).getReg other = s.getReg other := by
  unfold constant
  split <;> simp [execInstrBr, MachineState.getReg_setReg_ne, different]

theorem constant_mem (s : MachineState) (r : Reg) (n : ℕ) :
    ((constant r n).foldl execInstrBr s).mem = s.mem := by
  cases r <;> unfold constant <;> split <;> rfl

theorem constant_pc (s : MachineState) (r : Reg) (n : ℕ) :
    ((constant r n).foldl execInstrBr s).pc =
      s.pc + BitVec.ofNat 64 (4 * (constant r n).length) :=
  Riscv.linear_fold_pc s _ (constant_ready s r n)

theorem signExtend12_nonnegative (n : ℕ) (hn : n < 2048) :
    signExtend12 (BitVec.ofNat 12 n) = BitVec.ofNat 64 n := by
  have msb : (BitVec.ofNat 12 n).msb = false := by
    rw [BitVec.msb_eq_false_iff_two_mul_lt]
    simp only [BitVec.toNat_ofNat]
    omega
  rw [signExtend12, BitVec.signExtend_eq_setWidth_of_msb_false msb]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

theorem literalValue_small (n : ℕ) (hn : n < 2048) : literalValue n = BitVec.ofNat 64 n := by
  rw [literalValue, if_pos hn, signExtend12_nonnegative n hn]

/-- Every table row address used by the decoder has a correct literal expansion. -/
theorem table_row_literal (row : Fin 36) :
    literalValue (Riscv.dataBase.toNat + row.val * 122 * 16) =
      BitVec.ofNat 64 (Riscv.dataBase.toNat + row.val * 122 * 16) := by
  have checked : ∀ row : Fin 36,
      literalValue (Riscv.dataBase.toNat + row.val * 122 * 16) =
        BitVec.ofNat 64 (Riscv.dataBase.toNat + row.val * 122 * 16) := by decide +kernel
  exact checked row

theorem signExtend13_nonnegative (n : ℕ) (hn : n < 4096) :
    signExtend13 (BitVec.ofNat 13 n) = BitVec.ofNat 64 n := by
  have msb : (BitVec.ofNat 13 n).msb = false := by
    rw [BitVec.msb_eq_false_iff_two_mul_lt]
    simp only [BitVec.toNat_ofNat]
    omega
  rw [signExtend13, BitVec.signExtend_eq_setWidth_of_msb_false msb]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

theorem whenZero_transition (s : MachineState) (r : Reg) (body : Code)
    (bound : body.length < 1023) (located : Riscv.CodeAt s s.pc (whenZero r body)) :
    step s = some (s.setPC (s.pc + if s.getReg r = 0 then 4 else
      BitVec.ofNat 64 (4 * (body.length + 1)))) := by
  rw [step, located.head]
  have hsign := signExtend13_nonnegative (4 * (body.length + 1)) (by omega)
  simp only [execInstrBr, show s.getReg .x0 = 0 from rfl,
    hsign]
  by_cases h : s.getReg r = 0#64 <;> simp [h]

theorem whenNonzero_transition (s : MachineState) (r : Reg) (body : Code)
    (bound : body.length < 1023) (located : Riscv.CodeAt s s.pc (whenNonzero r body)) :
    step s = some (s.setPC (s.pc + if s.getReg r = 0 then
      BitVec.ofNat 64 (4 * (body.length + 1)) else 4)) := by
  rw [step, located.head]
  have hsign := signExtend13_nonnegative (4 * (body.length + 1)) (by omega)
  simp only [execInstrBr, show s.getReg .x0 = 0 from rfl,
    hsign]
  by_cases h : s.getReg r = 0#64 <;> simp [h]

theorem whenZero_observe (fuel : ℕ) (s : MachineState) (r : Reg) (body : Code)
    (bound : body.length < 1023) (located : Riscv.CodeAt s s.pc (whenZero r body)) :
    Riscv.observe (fuel + 1) s = Riscv.observe fuel
      (s.setPC (s.pc + if s.getReg r = 0 then 4 else BitVec.ofNat 64 (4 * (body.length + 1)))) := by
  apply Riscv.observe_regular fuel s _ _ located.head _ (by simp)
    (whenZero_transition s r body bound located)
  simp only [Riscv.admittedInstruction, BitVec.toNat_ofNat, beq_iff_eq]
  omega

theorem whenNonzero_observe (fuel : ℕ) (s : MachineState) (r : Reg) (body : Code)
    (bound : body.length < 1023) (located : Riscv.CodeAt s s.pc (whenNonzero r body)) :
    Riscv.observe (fuel + 1) s = Riscv.observe fuel
      (s.setPC (s.pc + if s.getReg r = 0 then BitVec.ofNat 64 (4 * (body.length + 1)) else 4)) := by
  apply Riscv.observe_regular fuel s _ _ located.head _ (by simp)
    (whenNonzero_transition s r body bound located)
  simp only [Riscv.admittedInstruction, BitVec.toNat_ofNat, beq_iff_eq]
  omega

end OptimalOTS.RiscvUpperProgram
