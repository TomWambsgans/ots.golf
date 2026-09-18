import Submissions.RiscvUpper.Program
import Submissions.RiscvUpper.AssemblyMacros

/-! The decoder's two-word comparison and subtraction use ordinary RV64 instructions. -/

namespace OptimalOTS.RiscvUpperProgram

open RiscvZkvm.Rv64

/-- Interpret a low word and a high word as one unsigned 128-bit integer. -/
def joinWords (lo hi : Word) : BitVec 128 := hi ++ lo

theorem joinWords_toNat (lo hi : Word) :
    (joinWords lo hi).toNat = hi.toNat * 2 ^ 64 + lo.toNat := by
  rw [joinWords, BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt lo.isLt,
    Nat.shiftLeft_eq]

/-- The six instructions comparing the rank in `x20/x21` with the count in `x24/x25`. -/
def compareWords : Code :=
  [.SLTU .x26 .x21 .x25, .XOR .x27 .x21 .x25, .SLTIU .x27 .x27 1,
   .SLTU .x7 .x20 .x24, .AND .x27 .x27 .x7, .OR .x26 .x26 .x27]

/-- Subtract the count, propagating the low-word borrow into the high word. -/
def subtractWords : Code :=
  [.SLTU .x27 .x20 .x24, .SUB .x20 .x20 .x24,
   .SUB .x21 .x21 .x25, .SUB .x21 .x21 .x27]

/-- The selected-digit arm stores the position and updates the remaining sum and flag. -/
def chooseWords (slot digit : ℕ) : Code :=
  constant .x7 (14 - digit) ++
    [.SD .x8 .x7 (BitVec.ofNat 12 (8 * slot)),
     .ADDI .x22 .x22 (-(BitVec.ofNat 12 digit)), .ADDI .x23 .x0 1]

/-- Address calculation and the two table loads preceding the rank comparison. -/
def readCount (remaining digit : ℕ) : Code :=
  constant .x6 (Riscv.dataBase.toNat + remaining * 122 * 16) ++
    [.ADDI .x7 .x22 (-(BitVec.ofNat 12 digit)), .SLLI .x7 .x7 4, .ADD .x6 .x6 .x7,
     .LD .x24 .x6 0, .LD .x25 .x6 8]

def testDigitPrefix (digit : ℕ) : Code :=
  constant .x26 digit ++ [.SLTU .x26 .x22 .x26]

def tableAddress (remaining sum : ℕ) : Word :=
  BitVec.ofNat 64 (Riscv.dataBase.toNat + remaining * 122 * 16 + 16 * sum)

/-- The table memory invariant needed by the decoder. -/
def TableLoaded (s : MachineState) : Prop :=
  ∀ remaining < 36, ∀ sum ≤ 121,
    joinWords (s.getMem (tableAddress remaining sum))
      (s.getMem (tableAddress remaining sum + 8)) = BitVec.ofNat 128 (Forest.comp remaining sum)

theorem signExtend_digit_neg (digit : ℕ) (hd : digit < 15) :
    signExtend12 (-(BitVec.ofNat 12 digit)) = -(BitVec.ofNat 64 digit) := by
  interval_cases digit <;> rfl

theorem signExtend_small_nat (value : ℕ) (hv : value < 2048) :
    signExtend12 (BitVec.ofNat 12 value) = BitVec.ofNat 64 value := by
  have fits : value < 2 ^ 12 := by omega
  have msb : (BitVec.ofNat 12 value).msb = false := by
    rw [BitVec.msb_eq_decide, BitVec.toNat_ofNat, Nat.mod_eq_of_lt fits]
    simp only [show 2 ^ (12 - 1) = 2048 by decide, decide_eq_false_iff_not]
    omega
  rw [signExtend12, BitVec.signExtend_eq_setWidth_of_msb_false msb]
  exact BitVec.setWidth_ofNat_of_le_of_lt (by decide) fits

theorem chooseWords_flag (s : MachineState) (slot digit : ℕ) :
    (chooseWords slot digit |>.foldl execInstrBr s).getReg .x23 = 1 := by
  simp [chooseWords, List.foldl_append, execInstrBr, MachineState.getReg,
    MachineState.setReg, MachineState.setPC, signExtend12]

theorem chooseWords_sum (s : MachineState) (slot digit : ℕ) (hd : digit < 15) :
    (chooseWords slot digit |>.foldl execInstrBr s).getReg .x22 =
      s.getReg .x22 - BitVec.ofNat 64 digit := by
  have small : 14 - digit < 2048 := by omega
  simp [chooseWords, constant, small, execInstrBr,
    MachineState.getReg, MachineState.setReg, MachineState.setPC,
    MachineState.setMem, signExtend_digit_neg digit hd, BitVec.sub_eq_add_neg]

theorem chooseWords_rank (s : MachineState) (slot digit : ℕ) :
    joinWords ((chooseWords slot digit |>.foldl execInstrBr s).getReg .x20)
      ((chooseWords slot digit |>.foldl execInstrBr s).getReg .x21) =
      joinWords (s.getReg .x20) (s.getReg .x21) := by
  have small : 14 - digit < 2048 := by omega
  simp [chooseWords, constant, small, execInstrBr,
    MachineState.getReg, MachineState.setReg, MachineState.setPC, MachineState.setMem]

theorem chooseWords_position (s : MachineState) (slot digit : ℕ) (hslot : slot < 36) :
    (chooseWords slot digit |>.foldl execInstrBr s).getMem
      (s.getReg .x8 + BitVec.ofNat 64 (8 * slot)) = BitVec.ofNat 64 (14 - digit) := by
  have small : 14 - digit < 2048 := by omega
  have offset : 8 * slot < 2048 := by omega
  simp [chooseWords, constant, small, execInstrBr, MachineState.getReg,
    MachineState.setReg, MachineState.setPC, MachineState.setMem, MachineState.getMem,
    signExtend_small_nat _ small, signExtend_small_nat _ offset]

theorem chooseWords_mem (s : MachineState) (slot digit : ℕ) (hslot : slot < 36) :
    (chooseWords slot digit |>.foldl execInstrBr s).mem =
      (s.setMem (s.getReg .x8 + BitVec.ofNat 64 (8 * slot))
        (BitVec.ofNat 64 (14 - digit))).mem := by
  have small : 14 - digit < 2048 := by omega
  have offset : 8 * slot < 2048 := by omega
  simp [chooseWords, constant, small, execInstrBr, MachineState.getReg,
    MachineState.setReg, MachineState.setPC, MachineState.setMem,
    signExtend_small_nat _ small, signExtend_small_nat _ offset]

theorem getReg_setMem (s : MachineState) (address value : Word) (r : Reg) :
    (s.setMem address value).getReg r = s.getReg r := by cases r <;> rfl

theorem chooseWords_preserves (s : MachineState) (slot digit : ℕ) (r : Reg)
    (h7 : r ≠ .x7) (h22 : r ≠ .x22) (h23 : r ≠ .x23) :
    (chooseWords slot digit |>.foldl execInstrBr s).getReg r = s.getReg r := by
  simp [chooseWords, List.foldl_append, execInstrBr, getReg_setMem,
    MachineState.getReg_setReg_ne, constant_preserves,
    Ne.symm h7, Ne.symm h22, Ne.symm h23]

theorem chooseWords_remaining (s : MachineState) (slot digit sum : ℕ)
    (hd : digit < 15) (hs : s.getReg .x22 = BitVec.ofNat 64 sum)
    (small : sum ≤ 121) (le : digit ≤ sum) :
    ((chooseWords slot digit |>.foldl execInstrBr s).getReg .x22).toNat = sum - digit := by
  rw [chooseWords_sum s slot digit hd, hs, BitVec.toNat_sub_of_le]
  · simp only [BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  · change sum % 2 ^ 64 ≥ digit % 2 ^ 64
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    exact le

theorem tableAddress_calculation (remaining sum digit : ℕ) (hs : sum ≤ 121)
    (hd : digit ≤ sum) :
    BitVec.ofNat 64 (Riscv.dataBase.toNat + remaining * 122 * 16) +
      ((BitVec.ofNat 64 sum - BitVec.ofNat 64 digit) <<< 4) =
        tableAddress remaining (sum - digit) := by
  rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by omega) hd, BitVec.shiftLeft_eq_mul_twoPow,
    show BitVec.twoPow 64 4 = BitVec.ofNat 64 16 by rfl, ← BitVec.ofNat_mul,
    ← BitVec.ofNat_add]
  unfold tableAddress
  congr 1
  omega

theorem readCount_value (s : MachineState) (remaining digit sum : ℕ)
    (row : remaining < 36) (small : sum ≤ 121) (digitBound : digit < 15)
    (allowed : digit ≤ sum) (reg : s.getReg .x22 = BitVec.ofNat 64 sum)
    (table : TableLoaded s) :
    joinWords ((readCount remaining digit |>.foldl execInstrBr s).getReg .x24)
      ((readCount remaining digit |>.foldl execInstrBr s).getReg .x25) =
        BitVec.ofNat 128 (Forest.comp remaining (sum - digit)) := by
  have literal := table_row_literal ⟨remaining, row⟩
  have memory := constant_mem s .x6 (Riscv.dataBase.toNat + remaining * 122 * 16)
  have query := table remaining row (sum - digit) (by omega)
  simp only [readCount, List.foldl_append, List.foldl_cons, List.foldl_nil, execInstrBr,
    MachineState.getReg_setPC, MachineState.getMem_setPC, MachineState.getMem_setReg]
  simp [MachineState.getReg_setReg_ne, MachineState.getReg_setReg_eq,
    constant_value, constant_preserves, signExtend_digit_neg digit digitBound,
    literal, reg, BitVec.add_neg_eq_sub, tableAddress_calculation remaining sum digit small allowed,
    MachineState.getMem, memory] at query ⊢
  change joinWords (s.mem (tableAddress remaining (sum - digit) + 0#64))
    (s.mem (tableAddress remaining (sum - digit) + 8#64)) = _
  simpa only [BitVec.add_zero] using query

theorem readCount_preserves (s : MachineState) (remaining digit : ℕ) (r : Reg)
    (h6 : r ≠ .x6) (h7 : r ≠ .x7) (h24 : r ≠ .x24) (h25 : r ≠ .x25) :
    (readCount remaining digit |>.foldl execInstrBr s).getReg r = s.getReg r := by
  simp [readCount, List.foldl_append, execInstrBr, MachineState.getReg_setReg_ne,
    constant_preserves, Ne.symm h6, Ne.symm h7, Ne.symm h24, Ne.symm h25]

theorem readCount_mem (s : MachineState) (remaining digit : ℕ) :
    (readCount remaining digit |>.foldl execInstrBr s).mem = s.mem := by
  simp only [readCount, List.foldl_append, List.foldl_cons, List.foldl_nil, execInstrBr]
  change (List.foldl execInstrBr s (constant .x6
    (Riscv.dataBase.toNat + remaining * 122 * 16))).mem = s.mem
  exact constant_mem _ _ _

set_option maxRecDepth 100000 in
theorem tableAddress_valid_checked : ∀ row : Fin 36, ∀ sum : Fin 122,
    isValidDwordAccess (tableAddress row sum) = true ∧
      isValidDwordAccess (tableAddress row sum + 8) = true := by decide +kernel

theorem tableAddress_valid (row sum : ℕ) (hr : row < 36) (hs : sum ≤ 121) :
    isValidDwordAccess (tableAddress row sum) = true ∧
      isValidDwordAccess (tableAddress row sum + 8) = true :=
  tableAddress_valid_checked ⟨row, hr⟩ ⟨sum, by omega⟩

theorem readCount_ready (s : MachineState) (remaining digit sum : ℕ)
    (row : remaining < 36) (small : sum ≤ 121) (digitBound : digit < 15)
    (allowed : digit ≤ sum) (reg : s.getReg .x22 = BitVec.ofNat 64 sum) :
    Riscv.LinearReady s (readCount remaining digit) := by
  have literal := table_row_literal ⟨remaining, row⟩
  have address := tableAddress_valid remaining (sum - digit) row (by omega)
  apply Riscv.LinearReady.append (constant_ready s .x6 _)
  simp only [Riscv.LinearReady, Riscv.linearInstruction, Riscv.memoryReady, true_and,
    and_true, execInstrBr, MachineState.getReg_setPC]
  simp [MachineState.getReg_setReg_ne, MachineState.getReg_setReg_eq,
    constant_value, constant_preserves, signExtend_digit_neg digit digitBound,
    literal, reg, BitVec.add_neg_eq_sub,
    tableAddress_calculation remaining sum digit small allowed]
  simpa [signExtend12, Nat.mod_eq_of_lt (tableAddress remaining (sum - digit)).isLt] using address

theorem compareWords_ready (s : MachineState) : Riscv.LinearReady s compareWords := by
  simp [compareWords, Riscv.LinearReady, Riscv.linearInstruction, Riscv.memoryReady]

theorem subtractWords_ready (s : MachineState) : Riscv.LinearReady s subtractWords := by
  simp [subtractWords, Riscv.LinearReady, Riscv.linearInstruction, Riscv.memoryReady]

theorem positionAddress_valid (slot : Fin 36) :
    isValidDwordAccess (BitVec.ofNat 64 positionsBase + BitVec.ofNat 64 (8 * slot.val)) = true := by
  have checked : ∀ slot : Fin 36,
      isValidDwordAccess (BitVec.ofNat 64 positionsBase + BitVec.ofNat 64 (8 * slot.val)) = true :=
    by decide +kernel
  exact checked slot

theorem chooseWords_ready (s : MachineState) (slot digit : ℕ) (hslot : slot < 36)
    (base : s.getReg .x8 = BitVec.ofNat 64 positionsBase) :
    Riscv.LinearReady s (chooseWords slot digit) := by
  have offset : 8 * slot < 2048 := by omega
  have address := positionAddress_valid ⟨slot, hslot⟩
  apply Riscv.LinearReady.append (constant_ready s .x7 _)
  simpa [Riscv.LinearReady, Riscv.linearInstruction, Riscv.memoryReady,
    constant_preserves, signExtend_small_nat _ offset, base] using address

theorem testDigitPrefix_ready (s : MachineState) (digit : ℕ) :
    Riscv.LinearReady s (testDigitPrefix digit) := by
  apply Riscv.LinearReady.append (constant_ready s .x26 digit)
  simp [Riscv.LinearReady, Riscv.linearInstruction, Riscv.memoryReady]

theorem testDigitPrefix_preserves (s : MachineState) (digit : ℕ) (r : Reg) (h : r ≠ .x26) :
    (testDigitPrefix digit |>.foldl execInstrBr s).getReg r = s.getReg r := by
  simp [testDigitPrefix, List.foldl_append, execInstrBr,
    MachineState.getReg_setReg_ne, constant_preserves, Ne.symm h]

theorem testDigitPrefix_mem (s : MachineState) (digit : ℕ) :
    (testDigitPrefix digit |>.foldl execInstrBr s).mem = s.mem := by
  simp only [testDigitPrefix, List.foldl_append, List.foldl_cons, List.foldl_nil, execInstrBr]
  exact constant_mem _ _ _

theorem testDigitPrefix_flag (s : MachineState) (sum digit : ℕ) (hs : sum ≤ 121)
    (hd : digit < 15) (reg : s.getReg .x22 = BitVec.ofNat 64 sum) :
    (testDigitPrefix digit |>.foldl execInstrBr s).getReg .x26 =
      if sum < digit then 1 else 0 := by
  simp [testDigitPrefix, List.foldl_append, execInstrBr,
    MachineState.getReg_setReg_eq, constant_preserves, constant_value,
    literalValue_small digit (by omega), reg, BitVec.ult_iff_toNat_lt]
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

theorem compare_word_values (lo hi countLo countHi : Word) :
    ((if hi.ult countHi then (1 : Word) else 0) |||
      ((if (hi ^^^ countHi).ult 1 then (1 : Word) else 0) &&&
        (if lo.ult countLo then (1 : Word) else 0))) =
    (if (joinWords lo hi).ult (joinWords countLo countHi) then 1 else 0) := by
  have equal : ((hi ^^^ countHi).ult 1 = true) ↔ hi = countHi := by
    rw [BitVec.ult_iff_lt]
    exact (BitVec.lt_one_iff (w := 64) (x := hi ^^^ countHi) (by decide)).trans
      BitVec.xor_eq_zero_iff
  have compare : ((joinWords lo hi).ult (joinWords countLo countHi) = true) ↔
      hi.toNat < countHi.toNat ∨ (hi = countHi ∧ lo.toNat < countLo.toNat) := by
    rw [BitVec.ult_iff_toNat_lt, joinWords_toNat, joinWords_toNat]
    have hl := lo.isLt
    have hc := countLo.isLt
    rw [← BitVec.toNat_inj]
    omega
  simp only [equal, compare, BitVec.ult_iff_toNat_lt]
  by_cases high : hi.toNat < countHi.toNat
  · have different : hi ≠ countHi := by intro h; subst hi; omega
    simp [high, different]
  · by_cases same : hi = countHi <;> by_cases low : lo.toNat < countLo.toNat <;>
      simp [high, same, low]

theorem subtract_word_values (lo hi countLo countHi : Word) :
    joinWords (lo - countLo)
      (hi - countHi - (if lo.ult countLo then (1 : Word) else 0)) =
    joinWords lo hi - joinWords countLo countHi := by
  apply BitVec.eq_of_toNat_eq
  simp only [joinWords_toNat, BitVec.toNat_sub]
  have hl := lo.isLt
  have hh := hi.isLt
  have hcl := countLo.isLt
  have hch := countHi.isLt
  simp only [BitVec.ult_iff_toNat_lt]
  split_ifs <;>
    simp only [show (1 : Word).toNat = 1 by rfl, show (0 : Word).toNat = 0 by rfl] <;>
    norm_num at * <;> omega

/-- The actual compare instructions leave `x26` equal to the unsigned comparison bit. -/
theorem compareWords_result (s : MachineState) :
    ((compareWords.foldl execInstrBr s).getReg .x26) =
    (if (joinWords (s.getReg .x20) (s.getReg .x21)).ult
        (joinWords (s.getReg .x24) (s.getReg .x25)) then 1 else 0) := by
  exact compare_word_values (s.getReg .x20) (s.getReg .x21)
    (s.getReg .x24) (s.getReg .x25)

theorem compareWords_preserves (s : MachineState) (r : Reg)
    (h7 : r ≠ .x7) (h26 : r ≠ .x26) (h27 : r ≠ .x27) :
    (compareWords.foldl execInstrBr s).getReg r = s.getReg r := by
  simp [compareWords, execInstrBr, MachineState.getReg_setReg_ne,
    Ne.symm h7, Ne.symm h26, Ne.symm h27]

theorem compareWords_mem (s : MachineState) : (compareWords.foldl execInstrBr s).mem = s.mem := rfl

theorem compareWords_lt_iff (s : MachineState) :
    (compareWords.foldl execInstrBr s).getReg .x26 ≠ 0 ↔
      (joinWords (s.getReg .x20) (s.getReg .x21)).toNat <
        (joinWords (s.getReg .x24) (s.getReg .x25)).toNat := by
  rw [compareWords_result]
  simp only [BitVec.ult_iff_toNat_lt]
  split_ifs <;> simp_all

/-- The actual subtraction instructions compute subtraction modulo `2^128`. -/
theorem subtractWords_result (s : MachineState) :
    joinWords ((subtractWords.foldl execInstrBr s).getReg .x20)
      ((subtractWords.foldl execInstrBr s).getReg .x21) =
    joinWords (s.getReg .x20) (s.getReg .x21) -
      joinWords (s.getReg .x24) (s.getReg .x25) := by
  simpa [subtractWords, execInstrBr, MachineState.getReg, MachineState.setReg,
    MachineState.setPC] using
    subtract_word_values (s.getReg .x20) (s.getReg .x21) (s.getReg .x24) (s.getReg .x25)

theorem subtractWords_preserves (s : MachineState) (r : Reg)
    (h20 : r ≠ .x20) (h21 : r ≠ .x21) (h27 : r ≠ .x27) :
    (subtractWords.foldl execInstrBr s).getReg r = s.getReg r := by
  simp [subtractWords, execInstrBr, MachineState.getReg_setReg_ne,
    Ne.symm h20, Ne.symm h21, Ne.symm h27]

theorem subtractWords_mem (s : MachineState) : (subtractWords.foldl execInstrBr s).mem = s.mem := rfl

/-- On the subtraction branch there is no 128-bit underflow, so the natural rank decreases
by exactly the table count. -/
theorem subtractWords_rank (s : MachineState)
    (h : (joinWords (s.getReg .x24) (s.getReg .x25)).toNat ≤
      (joinWords (s.getReg .x20) (s.getReg .x21)).toNat) :
    (joinWords ((subtractWords.foldl execInstrBr s).getReg .x20)
      ((subtractWords.foldl execInstrBr s).getReg .x21)).toNat =
    (joinWords (s.getReg .x20) (s.getReg .x21)).toNat -
      (joinWords (s.getReg .x24) (s.getReg .x25)).toNat := by
  rw [subtractWords_result, BitVec.toNat_sub_of_le]
  exact h

/-- The compare block followed by its guarded subtraction. This is the arithmetic part of
`tryDigit`; `x26` retains the decision used by the following choose branch. -/
def compareAndSubtract (s : MachineState) : MachineState :=
  let compared := compareWords.foldl execInstrBr s
  if compared.getReg .x26 = 0 then subtractWords.foldl execInstrBr compared else compared

theorem compareAndSubtract_choice (s : MachineState) :
    (compareAndSubtract s).getReg .x26 =
      if (joinWords (s.getReg .x20) (s.getReg .x21)).toNat <
          (joinWords (s.getReg .x24) (s.getReg .x25)).toNat then 1 else 0 := by
  dsimp only [compareAndSubtract]
  by_cases h : (compareWords.foldl execInstrBr s).getReg .x26 = 0
  · rw [if_pos h, subtractWords_preserves _ .x26 (by decide) (by decide) (by decide)]
    simpa only [BitVec.ult_iff_toNat_lt] using compareWords_result s
  · rw [if_neg h]
    simpa only [BitVec.ult_iff_toNat_lt] using compareWords_result s

theorem compareAndSubtract_rank (s : MachineState) :
    (joinWords ((compareAndSubtract s).getReg .x20)
      ((compareAndSubtract s).getReg .x21)).toNat =
      if (joinWords (s.getReg .x20) (s.getReg .x21)).toNat <
          (joinWords (s.getReg .x24) (s.getReg .x25)).toNat then
        (joinWords (s.getReg .x20) (s.getReg .x21)).toNat
      else (joinWords (s.getReg .x20) (s.getReg .x21)).toNat -
        (joinWords (s.getReg .x24) (s.getReg .x25)).toNat := by
  have frame (r : Reg) (h7 : r ≠ .x7) (h26 : r ≠ .x26) (h27 : r ≠ .x27) :=
    compareWords_preserves s r h7 h26 h27
  have compare := compareWords_lt_iff s
  dsimp only [compareAndSubtract]
  by_cases h : (compareWords.foldl execInstrBr s).getReg .x26 = 0
  · rw [if_pos h]
    have notLt : ¬ (joinWords (s.getReg .x20) (s.getReg .x21)).toNat <
        (joinWords (s.getReg .x24) (s.getReg .x25)).toNat :=
      fun lt => (compare.mpr lt) h
    rw [if_neg notLt]
    have hle : (joinWords ((compareWords.foldl execInstrBr s).getReg .x24)
        ((compareWords.foldl execInstrBr s).getReg .x25)).toNat ≤
        (joinWords ((compareWords.foldl execInstrBr s).getReg .x20)
          ((compareWords.foldl execInstrBr s).getReg .x21)).toNat := by
      simp only [frame .x20 (by decide) (by decide) (by decide),
        frame .x21 (by decide) (by decide) (by decide),
        frame .x24 (by decide) (by decide) (by decide),
        frame .x25 (by decide) (by decide) (by decide)]
      exact Nat.le_of_not_gt notLt
    rw [subtractWords_rank _ hle]
    simp only [frame .x20 (by decide) (by decide) (by decide),
      frame .x21 (by decide) (by decide) (by decide),
      frame .x24 (by decide) (by decide) (by decide),
      frame .x25 (by decide) (by decide) (by decide)]
  · rw [if_neg h, if_pos (compare.mp h)]
    simp only [frame .x20 (by decide) (by decide) (by decide),
      frame .x21 (by decide) (by decide) (by decide)]

theorem compareAndSubtract_preserves (s : MachineState) (r : Reg)
    (h7 : r ≠ .x7) (h20 : r ≠ .x20) (h21 : r ≠ .x21)
    (h26 : r ≠ .x26) (h27 : r ≠ .x27) :
    (compareAndSubtract s).getReg r = s.getReg r := by
  dsimp only [compareAndSubtract]
  split_ifs <;> simp only [subtractWords_preserves _ r h20 h21 h27,
    compareWords_preserves _ r h7 h26 h27]

theorem compareAndSubtract_mem (s : MachineState) : (compareAndSubtract s).mem = s.mem := by
  dsimp only [compareAndSubtract]
  split_ifs <;> rfl

/-- The complete compare/subtract/choose data transition after loading a table count. -/
def applyDigit (s : MachineState) (slot digit : ℕ) : MachineState :=
  let reduced := compareAndSubtract s
  if reduced.getReg .x26 = 0 then reduced else (chooseWords slot digit).foldl execInstrBr reduced

theorem applyDigit_flag (s : MachineState) (slot digit : ℕ) :
    (applyDigit s slot digit).getReg .x23 =
      if (joinWords (s.getReg .x20) (s.getReg .x21)).toNat <
        (joinWords (s.getReg .x24) (s.getReg .x25)).toNat then 1 else s.getReg .x23 := by
  dsimp only [applyDigit]
  rw [compareAndSubtract_choice]
  split_ifs <;> simp_all [chooseWords_flag, compareAndSubtract_preserves]

theorem applyDigit_rank (s : MachineState) (slot digit : ℕ) :
    (joinWords ((applyDigit s slot digit).getReg .x20)
      ((applyDigit s slot digit).getReg .x21)).toNat =
      if (joinWords (s.getReg .x20) (s.getReg .x21)).toNat <
        (joinWords (s.getReg .x24) (s.getReg .x25)).toNat then
        (joinWords (s.getReg .x20) (s.getReg .x21)).toNat
      else (joinWords (s.getReg .x20) (s.getReg .x21)).toNat -
        (joinWords (s.getReg .x24) (s.getReg .x25)).toNat := by
  dsimp only [applyDigit]
  by_cases h : (compareAndSubtract s).getReg .x26 = 0
  · rw [if_pos h]
    exact compareAndSubtract_rank s
  · rw [if_neg h, chooseWords_rank]
    exact compareAndSubtract_rank s

theorem applyDigit_sum (s : MachineState) (slot digit : ℕ) (hd : digit < 15) :
    (applyDigit s slot digit).getReg .x22 =
      if (joinWords (s.getReg .x20) (s.getReg .x21)).toNat <
        (joinWords (s.getReg .x24) (s.getReg .x25)).toNat then
        s.getReg .x22 - BitVec.ofNat 64 digit else s.getReg .x22 := by
  dsimp only [applyDigit]
  rw [compareAndSubtract_choice]
  split_ifs <;> simp_all [chooseWords_sum _ _ _ hd, compareAndSubtract_preserves]

theorem applyDigit_mem (s : MachineState) (slot digit : ℕ) (hs : slot < 36) :
    (applyDigit s slot digit).mem =
      if (joinWords (s.getReg .x20) (s.getReg .x21)).toNat <
        (joinWords (s.getReg .x24) (s.getReg .x25)).toNat then
        (s.setMem (s.getReg .x8 + BitVec.ofNat 64 (8 * slot))
          (BitVec.ofNat 64 (14 - digit))).mem
      else s.mem := by
  dsimp only [applyDigit]
  rw [compareAndSubtract_choice]
  split_ifs <;> simp_all [chooseWords_mem _ _ _ hs, MachineState.setMem,
    compareAndSubtract_mem, compareAndSubtract_preserves]

theorem applyDigit_preserves (s : MachineState) (slot digit : ℕ) (r : Reg)
    (h7 : r ≠ .x7) (h20 : r ≠ .x20) (h21 : r ≠ .x21)
    (h22 : r ≠ .x22) (h23 : r ≠ .x23) (h26 : r ≠ .x26) (h27 : r ≠ .x27) :
    (applyDigit s slot digit).getReg r = s.getReg r := by
  dsimp only [applyDigit]
  split_ifs <;> simp only [chooseWords_preserves _ _ _ r h7 h22 h23,
    compareAndSubtract_preserves _ r h7 h20 h21 h26 h27]

theorem TableLoaded.of_mem_eq {s t : MachineState} (table : TableLoaded s)
    (same : t.mem = s.mem) : TableLoaded t := by
  intro remaining hr sum hs
  simpa only [MachineState.getMem, same] using table remaining hr sum hs

theorem table_position_disjoint (remaining sum slot : ℕ) (hr : remaining < 36)
    (hs : sum ≤ 121) (hslot : slot < 36) :
    tableAddress remaining sum ≠ BitVec.ofNat 64 positionsBase + BitVec.ofNat 64 (8 * slot) ∧
      tableAddress remaining sum + 8 ≠
        BitVec.ofNat 64 positionsBase + BitVec.ofNat 64 (8 * slot) := by
  have disjoint (offset : ℕ) (ho : offset ≤ 8) :
      tableAddress remaining sum + BitVec.ofNat 64 offset ≠
        BitVec.ofNat 64 positionsBase + BitVec.ofNat 64 (8 * slot) := by
    intro h
    change BitVec.ofNat 64 (2097152 + remaining * 122 * 16 + 16 * sum) +
      BitVec.ofNat 64 offset = BitVec.ofNat 64 6291456 + BitVec.ofNat 64 (8 * slot) at h
    rw [← BitVec.ofNat_add, ← BitVec.ofNat_add] at h
    have eq := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat] at eq
    have leftBound : 2097152 + remaining * 122 * 16 + 16 * sum + offset < 2 ^ 64 := by omega
    have rightBound : 6291456 + 8 * slot < 2 ^ 64 := by omega
    rw [Nat.mod_eq_of_lt leftBound, Nat.mod_eq_of_lt rightBound] at eq
    omega
  constructor
  · simpa only [show BitVec.ofNat 64 0 = 0#64 by rfl, BitVec.add_zero] using disjoint 0 (by decide)
  · exact disjoint 8 le_rfl

theorem TableLoaded.setPosition {s : MachineState} (table : TableLoaded s)
    (slot : ℕ) (value : Word) (hs : slot < 36) :
    TableLoaded (s.setMem (BitVec.ofNat 64 positionsBase + BitVec.ofNat 64 (8 * slot)) value) := by
  intro remaining hr sum hsum
  have disjoint := table_position_disjoint remaining sum slot hr hsum hs
  simpa only [MachineState.getMem_setMem_ne disjoint.1,
    MachineState.getMem_setMem_ne disjoint.2] using table remaining hr sum hsum

theorem chooseWords_table (s : MachineState) (slot digit : ℕ) (hs : slot < 36)
    (table : TableLoaded s) (base : s.getReg .x8 = BitVec.ofNat 64 positionsBase) :
    TableLoaded (chooseWords slot digit |>.foldl execInstrBr s) := by
  apply (table.setPosition slot (BitVec.ofNat 64 (14 - digit)) hs).of_mem_eq
  rw [chooseWords_mem s slot digit hs, base]

end OptimalOTS.RiscvUpperProgram
