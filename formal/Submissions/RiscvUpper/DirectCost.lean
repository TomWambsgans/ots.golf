import Submissions.RiscvUpper.NodeProgram
import Submissions.RiscvUpper.LengthGuard

/-! A universal cycle bound for the direct node implementation. -/

namespace OptimalOTS.RiscvUpperProgram.Direct

open RiscvZkvm.Rv64 OracleComp

set_option maxRecDepth 500000 in
theorem verifier_lengthSafe : verifier.all lengthSafe = true := by decide +kernel

theorem loaded_lengthSafe (pc : Word) (i : Instr)
    (fetch : loadProgram Riscv.codeBase verifier pc = some i) : lengthSafe i = true := by
  unfold loadProgram at fetch
  dsimp only at fetch
  split_ifs at fetch
  exact List.all_eq_true.mp verifier_lengthSafe i (List.mem_of_getElem? fetch)

theorem initial_code (pk : PublicKey paperParams) (m : Message paperParams) (bits : List Bool) :
    (Riscv.initialState image pk m bits).code = loadProgram Riscv.codeBase verifier := by
  simp only [Riscv.initialState, MachineState.code_setReg,
    MachineState.code_writeBytesAsWords]
  rfl

theorem initial_pc (pk : PublicKey paperParams) (m : Message paperParams) (bits : List Bool) :
    (Riscv.initialState image pk m bits).pc = Riscv.codeBase := by
  simp [Riscv.initialState]

theorem initial_fetch (pk : PublicKey paperParams) (m : Message paperParams) (bits : List Bool) :
    let s := Riscv.initialState image pk m bits
    s.code s.pc = some (.ADDI .x11 .x0 0) := by
  dsimp only
  rw [initial_pc, initial_code]
  simp only [loadProgram, BitVec.sub_self, BitVec.toNat_ofNat, Nat.zero_mod,
    Nat.zero_div, verifier_length]
  rfl

theorem initial_step (pk : PublicKey paperParams) (m : Message paperParams) (bits : List Bool) :
    let s := Riscv.initialState image pk m bits
    step s = some ((s.setReg .x11 0).setPC (s.pc + 4)) := by
  dsimp only
  rw [step, initial_fetch]
  simp [execInstrBr, MachineState.getReg, signExtend12]

theorem after_initial_invariant (pk : PublicKey paperParams) (m : Message paperParams)
    (bits : List Bool) :
    let s := Riscv.initialState image pk m bits
    LengthInvariant ((s.setReg .x11 0).setPC (s.pc + 4)) := by
  constructor
  · simp [MachineState.getReg_setReg_eq]
  · simpa only [MachineState.code_setPC, MachineState.code_setReg, initial_code] using
      loaded_lengthSafe

/-- The fixed fuel gives a universal cycle bound, including every accepting path.
Termination and agreement with the OTS are separate obligations. -/
theorem execution_cost (pk : PublicKey paperParams) (m : Message paperParams) (bits : List Bool)
    (decision : Bool) (cycles : ℕ)
    (result : some (decision, cycles) ∈ support
      (Riscv.execute 114557 (Riscv.initialState image pk m bits))) : cycles ≤ 229113 := by
  rw [Riscv.execute_regular 114556 _ _ (initial_fetch pk m bits) (by decide) (by decide),
    initial_step] at result
  exact Riscv.addCycles_bound _ 1 (114556 * 2)
    (Riscv.execute_cost_of_invariant length_invariant (by decide) 114556 _
      (after_initial_invariant pk m bits)) decision cycles result

end OptimalOTS.RiscvUpperProgram.Direct
