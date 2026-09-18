import OptimalOTS.Riscv

/-! Kernel-checked boundary tests for the virtual machine, not OTS certificates. -/

open OptimalOTS OptimalOTS.Riscv RiscvZkvm.Rv64 OracleComp

namespace RiscvChecks

def state (code : List Instr) : MachineState :=
  { regs := fun _ => 0, mem := fun _ => 0, pc := codeBase,
    code := loadProgram codeBase code }

-- HALT itself is charged, and the accept/reject bit is explicit.
example : execute 1 (state [.ECALL]) = pure (some (false, 1)) := by rfl
example : execute 1 ((state [.ECALL]).setReg .x10 1) = pure (some (true, 1)) := by rfl
example : execute 1 ((state [.ECALL]).setReg .x10 2) = pure none := by rfl
example : execute 0 ((state [.ECALL]).setReg .x10 1) = pure none := by rfl

-- Real ADDI instructions cost one each; pseudo-instructions and host accelerators trap.
example : execute 2 (state [.ADDI .x10 .x0 1, .ECALL]) = pure (some (true, 2)) := by rfl
example : execute 2 (state [.LI .x10 1, .ECALL]) = pure none := by rfl
example : execute 1 (state [.CSRS 0 .x10]) = pure none := by rfl
example : execute 1 ((state [.ECALL]).setReg .x5 3) = pure none := by rfl
example : admittedInstruction (.BEQ .x0 .x0 3) = false := by decide

-- Input is packed little endian and partial bytes have zero high bits.
example : bytesOfBits [true, false, true] = [5] := by decide
example : bytesOfVector (0x0102 : BitVec 16) = [2, 1] := by decide

def hashState (bits : ℕ) : MachineState :=
  ((((state [.ECALL]).setReg .x5 hashCall).setReg .x10 dataBase).setReg .x11
    (BitVec.ofNat 64 bits)).setReg .x12 dataBase

example : hashArgumentsValid (hashState 513) = true := by decide
example : hashArgumentsValid ((hashState 0).setReg .x12 (dataBase + 1)) = false := by decide
example : (hashInput (hashState 0)).1 = 0 := by rfl
example : (hashInput (hashState 9)).1 = 9 := by rfl
example : hashInput ((hashState 9).setMem dataBase 0x0105) = ⟨9, (261 : BitVec 9)⟩ := by decide
example : blockCost paperParams 0 = 1 := by decide
example : blockCost paperParams 512 = 1 := by decide
example : blockCost paperParams 513 = 2 := by decide

-- An overlapping output buffer stores the answer in four little-endian doublewords.
example : (writeHash (hashState 9) (0x0201 : BitVec 256)).getByte dataBase = 1 := by decide
example : (writeHash (hashState 9) (0x0201 : BitVec 256)).getByte (dataBase + 1) = 2 := by decide

-- The hash syscall is the exact bare-oracle query, charged on its bit length.
example : execute 2 (hashState 513) = (do
    let answer ← hash paperParams (hashInput (hashState 513)).2
    addCycles 2 <$> execute 1 (writeHash (hashState 513) answer)) := by rfl

def hashThenAccept (bits : ℕ) : MachineState :=
  { hashState bits with code := (loadProgram codeBase
      [.ECALL, .ADDI .x5 .x0 0, .ADDI .x10 .x0 1, .ECALL]) }

example : execute 4 (hashThenAccept 513) = (do
    let _ ← hash paperParams (hashInput (hashThenAccept 513)).2
    pure (some (true, 5))) := by
  change (hash paperParams (hashInput (hashThenAccept 513)).2 >>= fun answer =>
    addCycles 2 <$> execute 3 (writeHash (hashThenAccept 513) answer)) = _
  apply bind_congr
  intro answer
  simp [execute, writeHash, hashThenAccept, hashState, state, admittedInstruction,
    loadProgram, step, execInstrBr, signExtend12, MachineState.getReg, MachineState.setReg,
    MachineState.setPC, MachineState.writeWords, MachineState.setMem,
    codeBase, addCycles]

def repeatedEmptyHash : MachineState :=
  { hashState 0 with code := (loadProgram codeBase
      [.ECALL, .ECALL, .ADDI .x5 .x0 0, .ADDI .x10 .x0 1, .ECALL]) }

-- Repeated identical queries still appear twice, and each costs one compression.
example : execute 5 repeatedEmptyHash = (do
    let _ ← hash paperParams (0 : BitVec 0)
    let _ ← hash paperParams (0 : BitVec 0)
    pure (some (true, 5))) := by
  change (hash paperParams (0 : BitVec 0) >>= fun answer =>
    addCycles 1 <$> execute 4 (writeHash repeatedEmptyHash answer)) = _
  apply bind_congr
  intro answer
  have zero_cost : blockCost paperParams 0 = 1 := by decide
  simp [execute, writeHash, repeatedEmptyHash, hashState, state, admittedInstruction,
    loadProgram, step, execInstrBr, signExtend12, MachineState.getReg, MachineState.setReg,
    MachineState.setPC, MachineState.writeWords, MachineState.setMem,
    codeBase, addCycles, hashCall, hashArgumentsValid, hashInput, dataBase,
    isValidOutputRange, isValidDwordAccess, MEM_START, MEM_END, INPUT_MEM_START,
    INPUT_MEM_END, RAM_MEM_START, RAM_MEM_END, zero_cost, ofBits]

-- Invalid return codes and fuel exhaustion are not interpreted as successful refinement.
example : (none : Outcome) ≠ some (false, 0) := by decide

end RiscvChecks
