import Submissions.RiscvUpper.AssemblyMacros

/-! Finite structured control flow for pure assembly regions. -/

namespace OptimalOTS.RiscvUpperProgram

open RiscvZkvm.Rv64

inductive PureBlock where
  | linear (instructions : Code)
  | seq (first last : PureBlock)
  | guard (zero : Bool) (reg : Reg) (body : PureBlock)

namespace PureBlock

def code : PureBlock → Code
  | .linear instructions => instructions
  | .seq first last => first.code ++ last.code
  | .guard zero r body => if zero then whenZero r body.code else whenNonzero r body.code

def passes (zero : Bool) (r : Reg) (s : MachineState) : Prop :=
  decide (s.getReg r = 0) = zero

instance (zero : Bool) (r : Reg) (s : MachineState) : Decidable (passes zero r s) :=
  inferInstanceAs (Decidable (decide (s.getReg r = 0) = zero))

def branchState (zero : Bool) (r : Reg) (length : ℕ) (s : MachineState) : MachineState :=
  s.setPC (s.pc + if passes zero r s then 4 else BitVec.ofNat 64 (4 * (length + 1)))

def eval : PureBlock → MachineState → MachineState
  | .linear instructions, s => instructions.foldl execInstrBr s
  | .seq first last, s => last.eval (first.eval s)
  | .guard zero r body, s =>
      if passes zero r s then body.eval (branchState zero r body.code.length s)
      else branchState zero r body.code.length s

def Ready : PureBlock → MachineState → Prop
  | .linear instructions, s => Riscv.LinearReady s instructions
  | .seq first last, s => first.Ready s ∧ last.Ready (first.eval s)
  | .guard zero r body, s => body.code.length < 1023 ∧
      (passes zero r s → body.Ready (branchState zero r body.code.length s))

theorem guard_code_length (zero : Bool) (r : Reg) (body : PureBlock) :
    (PureBlock.guard zero r body).code.length = body.code.length + 1 := by
  cases zero <;> rfl

theorem eval_code (b : PureBlock) (s : MachineState) : (b.eval s).code = s.code := by
  induction b generalizing s with
  | linear instructions => exact Riscv.fold_code s instructions
  | seq first last ihFirst ihLast => exact (ihLast _).trans (ihFirst s)
  | guard zero r body ih =>
    dsimp only [eval]
    split <;> simp only [ih, branchState, MachineState.code_setPC]

theorem eval_pc (b : PureBlock) (s : MachineState) (ready : b.Ready s) :
    (b.eval s).pc = s.pc + BitVec.ofNat 64 (4 * b.code.length) := by
  induction b generalizing s with
  | linear instructions => exact Riscv.linear_fold_pc s instructions ready
  | seq first last ihFirst ihLast =>
    rw [eval, ihLast _ ready.2, ihFirst _ ready.1]
    simp only [code, List.length_append, Nat.mul_add, BitVec.ofNat_add, BitVec.add_assoc]
  | guard zero r body ih =>
    rw [guard_code_length]
    dsimp only [eval]
    split_ifs with passed
    · rw [ih _ (ready.2 passed)]
      simp only [branchState, if_pos passed, MachineState.setPC,
        Nat.mul_add, Nat.mul_one, BitVec.ofNat_add]
      change (s.pc + 4) + BitVec.ofNat 64 (4 * body.code.length) =
        s.pc + (BitVec.ofNat 64 (4 * body.code.length) + 4)
      rw [BitVec.add_assoc, BitVec.add_comm (4 : Word)]
    · simp [branchState, passed, MachineState.setPC]

theorem branch_transition (zero : Bool) (r : Reg) (body : PureBlock) (s : MachineState)
    (bound : body.code.length < 1023)
    (located : Riscv.CodeAt s s.pc (PureBlock.guard zero r body).code) :
    step s = some (branchState zero r body.code.length s) := by
  cases zero with
  | true =>
    simpa only [branchState, passes, decide_eq_true_eq] using
      whenZero_transition s r body.code bound located
  | false =>
    have h := whenNonzero_transition s r body.code bound located
    simpa only [branchState, passes, decide_eq_false_iff_not, ite_not] using h

theorem branch_admitted (zero : Bool) (r : Reg) (body : PureBlock)
    (_bound : body.code.length < 1023) :
    Riscv.admittedInstruction ((PureBlock.guard zero r body).code.headD .ECALL) = true ∧
      (PureBlock.guard zero r body).code.headD .ECALL ≠ .ECALL := by
  cases zero <;> simp [code, whenZero, whenNonzero, Riscv.admittedInstruction,
    BitVec.toNat_ofNat] <;> omega

/-- Every valid structured block executes in at most its number of encoded instructions. -/
theorem steps (b : PureBlock) (s : MachineState)
    (ready : b.Ready s) (located : Riscv.CodeAt s s.pc b.code) :
    ∃ count, count ≤ b.code.length ∧ Riscv.PureSteps count s (b.eval s) := by
  induction b generalizing s with
  | linear instructions =>
    exact ⟨instructions.length, le_rfl, Riscv.linear_steps s instructions located ready⟩
  | seq first last ihFirst ihLast =>
    obtain ⟨n, hn, firstSteps⟩ := ihFirst s ready.1 located.append_left
    have rest : Riscv.CodeAt (first.eval s) (first.eval s).pc last.code := by
      rw [eval_pc first s ready.1]
      exact located.append_right.code_eq (eval_code first s)
    obtain ⟨m, hm, lastSteps⟩ := ihLast _ ready.2 rest
    refine ⟨n + m, ?_, firstSteps.trans lastSteps⟩
    simp only [code, List.length_append]
    omega
  | guard zero r body ih =>
    have fetch : s.code s.pc = some ((PureBlock.guard zero r body).code.headD .ECALL) := by
      cases zero <;> exact located.head
    have admitted := branch_admitted zero r body ready.1
    have transition := branch_transition zero r body s ready.1 located
    dsimp only [eval]
    split_ifs with passed
    · have tail : Riscv.CodeAt (branchState zero r body.code.length s)
          (branchState zero r body.code.length s).pc body.code := by
        change Riscv.CodeAt (branchState zero r body.code.length s)
          (s.pc + if passes zero r s then 4 else _) body.code
        rw [if_pos passed]
        have htail : Riscv.CodeAt s (s.pc + 4) body.code := by
          cases zero <;> exact located.tail
        exact htail.code_eq (by rfl)
      obtain ⟨n, hn, bodySteps⟩ := ih _ (ready.2 passed) tail
      refine ⟨n + 1, ?_, Riscv.PureSteps.cons fetch admitted.1 admitted.2 transition bodySteps⟩
      rw [guard_code_length]
      omega
    · refine ⟨1, ?_, Riscv.PureSteps.cons fetch admitted.1 admitted.2 transition
        (Riscv.PureSteps.refl _)⟩
      rw [guard_code_length]
      omega

/-- The number of instructions the block executes from `s`: guards charge their branch and only
the body actually taken. -/
def cost : PureBlock → MachineState → ℕ
  | .linear instructions, _ => instructions.length
  | .seq first last, s => first.cost s + last.cost (first.eval s)
  | .guard zero r body, s =>
      1 + if passes zero r s then body.cost (branchState zero r body.code.length s) else 0

theorem cost_le (b : PureBlock) (s : MachineState) : b.cost s ≤ b.code.length := by
  induction b generalizing s with
  | linear instructions => exact le_rfl
  | seq first last ihFirst ihLast =>
    simp only [cost, code, List.length_append]
    exact Nat.add_le_add (ihFirst s) (ihLast _)
  | guard zero r body ih =>
    simp only [cost]
    rw [guard_code_length]
    split_ifs
    · have := ih (branchState zero r body.code.length s); omega
    · omega

/-- Every block executes exactly `cost` instructions. -/
theorem steps_exact (b : PureBlock) (s : MachineState)
    (ready : b.Ready s) (located : Riscv.CodeAt s s.pc b.code) :
    Riscv.PureSteps (b.cost s) s (b.eval s) := by
  induction b generalizing s with
  | linear instructions => exact Riscv.linear_steps s instructions located ready
  | seq first last ihFirst ihLast =>
    have rest : Riscv.CodeAt (first.eval s) (first.eval s).pc last.code := by
      rw [eval_pc first s ready.1]
      exact located.append_right.code_eq (eval_code first s)
    exact (ihFirst s ready.1 located.append_left).trans (ihLast _ ready.2 rest)
  | guard zero r body ih =>
    have fetch : s.code s.pc = some ((PureBlock.guard zero r body).code.headD .ECALL) := by
      cases zero <;> exact located.head
    have admitted := branch_admitted zero r body ready.1
    have transition := branch_transition zero r body s ready.1 located
    dsimp only [eval, cost]
    split_ifs with passed
    · have tail : Riscv.CodeAt (branchState zero r body.code.length s)
          (branchState zero r body.code.length s).pc body.code := by
        change Riscv.CodeAt (branchState zero r body.code.length s)
          (s.pc + if passes zero r s then 4 else _) body.code
        rw [if_pos passed]
        have htail : Riscv.CodeAt s (s.pc + 4) body.code := by
          cases zero <;> exact located.tail
        exact htail.code_eq (by rfl)
      rw [Nat.add_comm]
      exact Riscv.PureSteps.cons fetch admitted.1 admitted.2 transition (ih _ (ready.2 passed) tail)
    · exact Riscv.PureSteps.cons fetch admitted.1 admitted.2 transition (Riscv.PureSteps.refl _)

/-- Control addresses do not affect the data computation in these blocks. -/
def DataEq (s t : MachineState) : Prop := s.regs = t.regs ∧ s.mem = t.mem

theorem DataEq.reg {s t : MachineState} (same : DataEq s t) (r : Reg) :
    s.getReg r = t.getReg r := by simp only [MachineState.getReg, same.1]

theorem DataEq.setPC {s t : MachineState} (same : DataEq s t) (p q : Word) :
    DataEq (s.setPC p) (t.setPC q) := same

theorem DataEq.exec {s t : MachineState} (same : DataEq s t) (i : Instr)
    (linear : Riscv.linearInstruction i = true) :
    DataEq (execInstrBr s i) (execInstrBr t i) := by
  cases s
  cases t
  obtain ⟨rfl, rfl⟩ := same
  cases i <;> simp_all only [Riscv.linearInstruction, Bool.false_eq_true]
  all_goals constructor <;> simp [execInstrBr, MachineState.setPC, MachineState.setReg,
    MachineState.getReg, MachineState.setMem, MachineState.getMem,
    MachineState.setHalfword, MachineState.setByte, MachineState.getByte]
  all_goals split <;> rfl

theorem DataEq.fold {s t : MachineState} (same : DataEq s t) (instructions : Code)
    (ready : Riscv.LinearReady s instructions) :
    DataEq (instructions.foldl execInstrBr s) (instructions.foldl execInstrBr t) := by
  induction instructions generalizing s t with
  | nil => exact same
  | cons i instructions ih => exact ih (same.exec i ready.1) ready.2.2

theorem DataEq.eval {s t : MachineState} (same : DataEq s t) (b : PureBlock)
    (ready : b.Ready s) : DataEq (b.eval s) (b.eval t) := by
  induction b generalizing s t with
  | linear instructions => exact same.fold instructions ready
  | seq first last ihFirst ihLast => exact ihLast (ihFirst same ready.1) ready.2
  | guard zero r body ih =>
    have hp : passes zero r s ↔ passes zero r t := by simp only [passes, same.reg r]
    change DataEq
      (if passes zero r s then body.eval (branchState zero r body.code.length s)
        else branchState zero r body.code.length s)
      (if passes zero r t then body.eval (branchState zero r body.code.length t)
        else branchState zero r body.code.length t)
    by_cases hs : passes zero r s
    · rw [if_pos hs, if_pos (hp.mp hs)]
      exact ih (same.setPC _ _) (ready.2 hs)
    · rw [if_neg hs, if_neg (mt hp.mpr hs)]
      exact same.setPC _ _

/-- A block can be composed with any proved continuation using its code length as a budget. -/
theorem observe_continuation (b : PureBlock) (s : MachineState) (ready : b.Ready s)
    (located : Riscv.CodeAt s s.pc b.code) (rest fuel : ℕ)
    (q : OracleComp (Spec paperParams) (Option Bool))
    (bound : b.code.length + rest ≤ fuel)
    (continuation : ∀ left, rest ≤ left → Riscv.observe left (b.eval s) = q) :
    Riscv.observe fuel s = q := by
  obtain ⟨used, hused, execution⟩ := b.steps s ready located
  have h := execution.observe (fuel - used)
  rw [Nat.add_sub_of_le (by omega : used ≤ fuel)] at h
  rw [h]
  exact continuation _ (by omega)

end PureBlock
end OptimalOTS.RiscvUpperProgram
