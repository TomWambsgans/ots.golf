import Submissions.RiscvUpper.MachineCost
import Submissions.RiscvUpper.Program

/-! The verifier keeps the hash-input length at most 912 bits after its first instruction. -/

namespace OptimalOTS.RiscvUpperProgram

open RiscvZkvm.Rv64 OracleComp

/-- Instructions used by this image either preserve `a1`, or set it to a fixed hash length. -/
def lengthSafe : Instr → Bool
  | .ADDI rd rs imm => decide (rd ≠ .x11 ∨ rs = .x0 ∧
      (imm = 0 ∨ imm = 144 ∨ imm = 400 ∨ imm = 512 ∨ imm = 912))
  | .LUI rd _ | .LD rd _ _ | .XOR rd _ _ | .SRLI rd _ _ | .SLTU rd _ _
  | .SLTIU rd _ _ | .AND rd _ _ | .OR rd _ _ | .SLLI rd _ _ | .ADD rd _ _
  | .SUB rd _ _ => decide (rd ≠ .x11)
  | .SD _ _ _ | .SH _ _ _ | .BEQ _ _ _ | .BNE _ _ _ | .ECALL => true
  | _ => false

theorem lengthSafe_exec (s : MachineState) (i : Instr)
    (hs : (s.getReg .x11).toNat ≤ 912) (hi : lengthSafe i = true) :
    ((execInstrBr s i).getReg .x11).toNat ≤ 912 := by
  cases i <;> simp only [lengthSafe, decide_eq_true_eq] at hi <;> try contradiction
  case ADDI rd rs imm =>
    rcases hi with different | ⟨rfl, hvalue⟩
    · simpa [execInstrBr, MachineState.getReg_setReg_ne, different] using hs
    · by_cases hr : rd = .x11
      · subst rd
        rcases hvalue with rfl | rfl | rfl | rfl | rfl <;>
          norm_num [execInstrBr, MachineState.getReg, MachineState.setReg,
            signExtend12, MachineState.setPC] <;> decide
      · simpa [execInstrBr, MachineState.getReg_setReg_ne, hr] using hs
  all_goals first
    | (simpa only [execInstrBr, MachineState.getReg_setPC,
        MachineState.getReg_setReg_ne _ _ _ _ hi] using hs)
    | exact hs
    | (simp only [execInstrBr]; split <;> exact hs)

theorem lengthSafe_step (s next : MachineState) (i : Instr)
    (fetch : s.code s.pc = some i) (hi : lengthSafe i = true) (ordinary : i ≠ .ECALL)
    (transition : step s = some next) : next = execInstrBr s i := by
  rw [step, fetch] at transition
  cases i <;> simp only [lengthSafe, decide_eq_true_eq] at hi <;> try contradiction
  all_goals dsimp only at transition
  all_goals first
    | exact (Option.some.inj transition).symm
    | (split_ifs at transition; exact (Option.some.inj transition).symm)

def LengthInvariant (s : MachineState) : Prop :=
  (s.getReg .x11).toNat ≤ 912 ∧ ∀ pc i, s.code pc = some i → lengthSafe i = true

theorem length_invariant : Riscv.CostInvariant LengthInvariant 2 where
  hashCost s hs := by
    have bound := hs.1
    unfold blockCost
    norm_num [paperParams]
    omega
  hashStep s hs answer := by
    constructor
    · simpa only [Riscv.writeHash, MachineState.getReg_setPC,
        MachineState.getReg_writeWords] using hs.1
    · simpa [Riscv.writeHash] using hs.2
  randomStep s hs word := by
    constructor
    · simpa [MachineState.getReg_setReg_ne] using hs.1
    · simpa using hs.2
  ordinaryStep s hs ordinary next transition := by
    cases fetch : s.code s.pc with
    | none => simp [step, fetch] at transition
    | some i =>
      have hi := hs.2 s.pc i fetch
      have hn : i ≠ .ECALL := by simpa [fetch] using ordinary
      constructor
      · rw [lengthSafe_step s next i fetch hi hn transition]
        exact lengthSafe_exec s i hs.1 hi
      · simpa only [code_step transition] using hs.2

set_option maxRecDepth 100000 in
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
      (Riscv.execute 29697 (Riscv.initialState image pk m bits))) : cycles ≤ 59393 := by
  rw [Riscv.execute_regular 29696 _ _ (initial_fetch pk m bits) (by decide) (by decide),
    initial_step] at result
  exact Riscv.addCycles_bound _ 1 (29696 * 2)
    (Riscv.execute_cost_of_invariant length_invariant (by decide) 29696 _
      (after_initial_invariant pk m bits)) decision cycles result

/--
info: 'OptimalOTS.RiscvUpperProgram.execution_cost' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms execution_cost

end OptimalOTS.RiscvUpperProgram
