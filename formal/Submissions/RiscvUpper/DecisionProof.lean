import Submissions.RiscvUpper.NodeProgram
import Submissions.RiscvUpper.CopyProof

/-! The final machine comparison accepts exactly the specified public key. -/

namespace OptimalOTS.RiscvUpperProgram.Direct

open RiscvZkvm.Rv64 Forest.Name

/-- All instructions before the final HALT. -/
def decisionPrefix : Code := decision.take 13

theorem decision_code : decision = decisionPrefix ++ [.ECALL] := by decide +kernel

theorem decisionPrefix_length : decisionPrefix.length = 13 := by decide +kernel

theorem decisionPrefix_ready (s : MachineState) : Riscv.LinearReady s decisionPrefix := by
  simp [decisionPrefix, decision, constant, slotAddress, slotsBase, idx, Forest.N,
    Riscv.LinearReady, Riscv.linearInstruction, Riscv.memoryReady, execInstrBr,
    MachineState.getReg, MachineState.setReg, MachineState.setPC, signExtend12,
    Riscv.publicKeyBase, MEM_START, MEM_END]

private theorem words_equal (a b c d : Word) :
    (if ((a ^^^ b) ||| (c ^^^ d)).ult 1 then (1 : Word) else 0) =
      BitVec.ofNat 64 (decide (a = b ∧ c = d)).toNat := by
  have hz (w : Word) : w.toNat = 0 ↔ w = 0 := by
    constructor
    · intro h
      exact BitVec.eq_of_toNat_eq h
    · rintro rfl
      rfl
  simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by norm_num : 1 < 2 ^ 64),
    Nat.lt_one_iff, hz, BitVec.or_eq_zero_iff, BitVec.xor_eq_zero_iff]
  by_cases h : a = b ∧ c = d <;> simp [h]
  intro hab hcd
  exact h ⟨BitVec.eq_of_toNat_eq hab, BitVec.eq_of_toNat_eq hcd⟩

set_option maxRecDepth 10000 in
/-- The four loaded words determine the machine's Boolean result. -/
theorem decisionPrefix_result (s : MachineState) :
    (decisionPrefix.foldl execInstrBr s).getReg .x10 = BitVec.ofNat 64
      (decide (s.getMem (BitVec.ofNat 64 (slotAddress rh)) = s.getMem Riscv.publicKeyBase ∧
        s.getMem (BitVec.ofNat 64 (slotAddress rh + 8)) = s.getMem (Riscv.publicKeyBase + 8))).toNat := by
  change (if ((s.getMem (BitVec.ofNat 64 (slotAddress rh)) ^^^ s.getMem Riscv.publicKeyBase) |||
      (s.getMem (BitVec.ofNat 64 (slotAddress rh + 8)) ^^^ s.getMem (Riscv.publicKeyBase + 8))).ult 1
        then (1 : Word) else 0) = _
  exact words_equal _ _ _ _

theorem decisionPrefix_call (s : MachineState) :
    (decisionPrefix.foldl execInstrBr s).getReg .x5 = 0 := rfl

private theorem split128_equal (a b : BitVec 128) :
    a.extractLsb' 0 64 = b.extractLsb' 0 64 ∧
      a.extractLsb' 64 64 = b.extractLsb' 64 64 ↔ a = b := by
  constructor
  · rintro ⟨lo, hi⟩
    calc
      a = a.extractLsb' 64 64 ++ a.extractLsb' 0 64 :=
        (BitVec.extractLsb'_append_extractLsb' (w := 64) (len := 64) (x := a)).symm
      _ = b.extractLsb' 64 64 ++ b.extractLsb' 0 64 := by rw [lo, hi]
      _ = b := BitVec.extractLsb'_append_extractLsb' (w := 64) (len := 64) (x := b)
  · rintro rfl
    exact ⟨rfl, rfl⟩

private theorem high_word {s : MachineState} {base : Word} {v : BitVec 128}
    (aligned : alignToDword (base + 8) = base + 8) (memory : MemBits s base v) :
    s.getMem (base + 8) = v.extractLsb' 64 64 := by
  have hm := memBits_extract (start := 64) (len := 64) memory (by decide) (by decide)
  have hw := getMem_of_memBits (by decide : 64 ≤ 64) aligned hm
  simpa using hw

/-- The instruction result agrees with the specification's 128-bit key comparison. -/
theorem decisionPrefix_correct (s : MachineState) (root pk : BitVec 128)
    (hroot : MemBits s (BitVec.ofNat 64 (slotAddress rh)) root)
    (hpk : MemBits s Riscv.publicKeyBase pk) :
    (decisionPrefix.foldl execInstrBr s).getReg .x10 =
      BitVec.ofNat 64 (decide (root = pk)).toNat := by
  rw [decisionPrefix_result,
    getMem_of_memBits (by decide) (by decide +kernel) hroot,
    getMem_of_memBits (by decide) (by decide +kernel) hpk]
  have hr := high_word (by decide +kernel) hroot
  have hp := high_word (by decide +kernel) hpk
  rw [show BitVec.ofNat 64 (slotAddress rh + 8) = BitVec.ofNat 64 (slotAddress rh) + 8 by rfl,
    hr, hp]
  simp only [split128_equal]

/-- The final block terminates and accepts exactly when the two keys agree. -/
theorem decision_observe (s : MachineState) (root pk : BitVec 128) (fuel : ℕ)
    (located : Riscv.CodeAt s s.pc decision)
    (hroot : MemBits s (BitVec.ofNat 64 (slotAddress rh)) root)
    (hpk : MemBits s Riscv.publicKeyBase pk) (bound : decision.length ≤ fuel) :
    Riscv.observe fuel s = pure (some (decide (root = pk))) := by
  rw [decision_code] at located bound
  have ready := decisionPrefix_ready s
  have rest : Riscv.CodeAt (decisionPrefix.foldl execInstrBr s)
      (decisionPrefix.foldl execInstrBr s).pc [.ECALL] := by
    rw [Riscv.linear_fold_pc _ _ ready]
    exact located.append_right.code_eq (Riscv.fold_code _ _)
  have enough : decisionPrefix.length + 1 ≤ fuel := by simpa using bound
  rw [show fuel = decisionPrefix.length + ((fuel - decisionPrefix.length - 1) + 1) by omega,
    Riscv.observe_linear _ _ _ located.append_left ready]
  exact Riscv.observe_halt _ _ _ rest.head (decisionPrefix_call s)
    (decisionPrefix_correct s root pk hroot hpk)

end OptimalOTS.RiscvUpperProgram.Direct
