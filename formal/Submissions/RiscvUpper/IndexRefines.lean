import Submissions.RiscvUpper.Refines
import Submissions.RiscvUpper.IndexExecution

/-! The index query and wire-format checks, with exact cycle accounting. -/

namespace OptimalOTS.RiscvUpperProgram

open RiscvZkvm.Rv64 OracleComp

theorem reject_refines (s : MachineState) (fuel : ℕ)
    (located : Riscv.CodeAt s s.pc reject) (bound : 3 ≤ fuel) :
    Riscv.Refines fuel s (pure (some false)) 3 := by
  let front : Code := [.ADDI .x5 .x0 0, .ADDI .x10 .x0 0]
  have ready : Riscv.LinearReady s front := by
    simp [front, Riscv.LinearReady, Riscv.linearInstruction, Riscv.memoryReady]
  have code : Riscv.CodeAt s s.pc (front ++ [.ECALL]) := located
  have pc : (front.foldl execInstrBr s).pc = s.pc + 8 := by
    simpa [front] using Riscv.linear_fold_pc s front ready
  have halt : Riscv.CodeAt (front.foldl execInstrBr s)
      (front.foldl execInstrBr s).pc [.ECALL] := by
    rw [pc]
    exact code.append_right.code_eq (Riscv.fold_code s front)
  have h := Riscv.Refines.linear front code.append_left ready
    (Riscv.Refines.halt (fuel := fuel - 3) false halt.head rfl rfl)
  have total : front.length + (fuel - 3 + 1) = fuel := by simp [front]; omega
  rw [total] at h
  exact h

/-- A failed check reaches HALT false; a passed check jumps over that block. -/
theorem checkedBranch_refines (s : MachineState) (fuel : ℕ)
    (located : Riscv.CodeAt s s.pc (whenNonzero .x26 reject)) (bound : 4 ≤ fuel)
    {q : OracleComp (Spec paperParams) (Option Bool)} {c : ℕ} (hc : 3 ≤ c)
    (h : s.getReg .x26 = 0#64 → Riscv.Refines (fuel - 1) (skipReject s) q c) :
    Riscv.Refines fuel s (if s.getReg .x26 = 0#64 then q else pure (some false)) (c + 1) := by
  have transition := whenNonzero_transition s .x26 reject (by decide) located
  change step s = some (s.setPC (s.pc + if s.getReg .x26 = 0#64 then 16 else 4)) at transition
  have fetch := located.head
  rw [show fuel = (fuel - 1) + 1 by omega]
  by_cases zero : s.getReg .x26 = 0#64
  · rw [if_pos zero]
    rw [if_pos zero] at transition
    exact Riscv.Refines.branch fetch (by decide) (by decide) transition (h zero)
  · rw [if_neg zero]
    rw [if_neg zero] at transition
    have rej := reject_refines (s.setPC (s.pc + 4)) (fuel - 1) (located.tail.code_eq rfl)
      (by omega)
    exact (Riscv.Refines.branch fetch (by decide) (by decide) transition rej).mono (by omega)

theorem capped_length_eq (bits : List Bool) :
    (5376 : Word) ^^^ BitVec.ofNat 64 (min bits.length 5377) = 0#64 ↔ bits.length = 5376 := by
  rw [BitVec.xor_eq_zero_iff]
  constructor
  · intro h
    have hn := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat] at hn
    have bound : min bits.length 5377 < 2 ^ 64 := by omega
    rw [Nat.mod_eq_of_lt bound] at hn
    change 5376 = min bits.length 5377 at hn
    omega
  · intro h
    simp [h]

/-- The suffix either rejects or reaches its continuation in 243 cycles. -/
theorem indexChecks_refines (s : MachineState) (fuel : ℕ)
    (scratch : s.getReg .x19 = BitVec.ofNat 64 scratchBase)
    (located : Riscv.CodeAt s s.pc indexChecks) (bound : 249 ≤ fuel)
    {q : OracleComp (Spec paperParams) (Option Bool)} {c : ℕ} (hc : 3 ≤ c)
    (h : Accepted (indexOf s) → (5376 : Word) ^^^ s.getReg .x13 = 0#64 →
      Riscv.Refines (fuel - 243) (checkedIndexState s) q c) :
    Riscv.Refines fuel s
      (if Accepted (indexOf s) ∧ (5376 : Word) ^^^ s.getReg .x13 = 0#64 then q
        else pure (some false)) (c + 243) := by
  have code : Riscv.CodeAt s s.pc
      (nibbleChecks ++ (whenNonzero .x26 reject ++
        (indexLengthCheck ++ whenNonzero .x26 reject))) := by
    simpa only [indexChecks, List.append_assoc] using located
  have ready := nibbleChecks_ready s scratch
  obtain ⟨aTest, -, a13, -, -, -, -, -⟩ := nibbleChecks_effect s
  have aPC := Riscv.linear_fold_pc s _ ready
  have aCodeEq := Riscv.fold_code s nibbleChecks
  unfold checkedIndexState at h
  generalize ha : nibbleChecks.foldl execInstrBr s = a at aTest a13 aPC aCodeEq h
  let b := skipReject a
  let d := indexLengthCheck.foldl execInstrBr b
  have aCode : Riscv.CodeAt a a.pc (whenNonzero .x26 reject ++
      (indexLengthCheck ++ whenNonzero .x26 reject)) := by
    rw [aPC]
    exact code.append_right.code_eq aCodeEq
  have bCode : Riscv.CodeAt b b.pc (indexLengthCheck ++ whenNonzero .x26 reject) :=
    aCode.append_right.code_eq rfl
  have dPC : d.pc = b.pc + BitVec.ofNat 64 (4 * indexLengthCheck.length) :=
    Riscv.linear_fold_pc b _ (indexLengthCheck_ready b)
  have dCode : Riscv.CodeAt d d.pc (whenNonzero .x26 reject) := by
    rw [dPC]
    exact bCode.append_right.code_eq (Riscv.fold_code b indexLengthCheck)
  have dTest : d.getReg .x26 = (5376 : Word) ^^^ s.getReg .x13 := by
    show (indexLengthCheck.foldl execInstrBr b).getReg .x26 = _
    rw [indexLengthCheck_test]
    change 5376 ^^^ a.getReg .x13 = _
    rw [a13]
  have checkLength : indexLengthCheck.length = 3 := rfl
  have step2 (hA : Accepted (indexOf s)) :
      Riscv.Refines (fuel - 242) d
        (if (5376 : Word) ^^^ s.getReg .x13 = 0#64 then q else pure (some false)) (c + 1) := by
    have hb := checkedBranch_refines d (fuel - 242) dCode (by omega) (q := q) (c := c) hc
      (fun hB => by
        rw [dTest] at hB
        have := h hA hB
        rw [show fuel - 243 = fuel - 242 - 1 by omega] at this
        exact this)
    rwa [dTest] at hb
  have step3 (hA : Accepted (indexOf s)) :
      Riscv.Refines (fuel - 239) b
        (if (5376 : Word) ^^^ s.getReg .x13 = 0#64 then q else pure (some false)) (c + 4) := by
    have := Riscv.Refines.linear indexLengthCheck bCode.append_left (indexLengthCheck_ready b)
      (step2 hA)
    rwa [checkLength, show 3 + (fuel - 242) = fuel - 239 by omega, show 3 + (c + 1) = c + 4 by omega]
      at this
  have step4 : Riscv.Refines (fuel - 238) a
      (if Accepted (indexOf s) then
        (if (5376 : Word) ^^^ s.getReg .x13 = 0#64 then q else pure (some false))
      else pure (some false)) (c + 4 + 1) := by
    have hb := checkedBranch_refines a (fuel - 238) aCode.append_left (by omega)
      (q := if (5376 : Word) ^^^ s.getReg .x13 = 0#64 then q else pure (some false))
      (c := c + 4) (by omega)
      (fun hA => by
        rw [aTest] at hA
        have := step3 hA
        rw [show fuel - 239 = fuel - 238 - 1 by omega] at this
        exact this)
    exact hb.congr (if_congr aTest rfl rfl)
  rw [← ha] at step4
  have step5 := Riscv.Refines.linear nibbleChecks code.append_left ready step4
  rw [nibbleChecks_length, show 238 + (fuel - 238) = fuel by omega] at step5
  refine (step5.congr ?_).mono (by omega)
  by_cases hA : Accepted (indexOf s)
  · by_cases hB : (5376 : Word) ^^^ s.getReg .x13 = 0#64
    · rw [if_pos hA, if_pos hB, if_pos ⟨hA, hB⟩]
    · rw [if_pos hA, if_neg hB, if_neg (fun h => hB h.2)]
  · rw [if_neg hA, if_neg (fun h => hA h.1)]

/-- The machine issues the specified first query, rejects exactly the invalid index and length
cases, and otherwise enters any proved continuation, at 267 cycles plus the continuation. -/
theorem indexAndChecks_refines (image : Riscv.Image) (pk : PublicKey paperParams)
    (m : Message paperParams) (bits : List Bool) (hdata : image.data.length ≤ 1048576)
    (rest fuel : ℕ) (q : BitVec 256 → OracleComp (Spec paperParams) (Option Bool)) (c : ℕ)
    (hc : 3 ≤ c)
    (located : Riscv.CodeAt (Riscv.initialState image pk m bits)
      (Riscv.initialState image pk m bits).pc indexAndChecks)
    (bound : indexAndChecks.length + rest ≤ fuel)
    (continuation : ∀ answer, Accepted (answer.setWidth 128).toNat → bits.length = 5376 →
      ∀ left, rest ≤ left →
        Riscv.Refines left
          (checkedIndexState (Riscv.writeHash (indexInputState image pk m bits) answer))
          (q answer) c) :
    Riscv.Refines fuel (Riscv.initialState image pk m bits) (do
      let answer ← hash paperParams (m ++ ofBits 128 bits)
      if Accepted (answer.setWidth 128).toNat ∧ bits.length = 5376 then q answer
      else pure (some false)) (c + 267) := by
  rw [indexAndChecks_parts] at located
  have ready := indexPrefix_ready image pk m bits
  have callLocated : Riscv.CodeAt (indexInputState image pk m bits)
      (indexInputState image pk m bits).pc (.ECALL :: indexChecks) := by
    change Riscv.CodeAt (indexInputState image pk m bits)
      (indexPrefix.foldl execInstrBr (Riscv.initialState image pk m bits)).pc _
    rw [Riscv.linear_fold_pc _ _ ready]
    exact located.append_right.code_eq (Riscv.fold_code _ _)
  have length := indexPrefix_length
  have enough : 273 + rest ≤ fuel := by simpa only [indexAndChecks_length] using bound
  have afterHash : ∀ answer, Riscv.Refines (fuel - 24)
      (Riscv.writeHash (indexInputState image pk m bits) answer)
      (if Accepted (answer.setWidth 128).toNat ∧ bits.length = 5376 then q answer
        else pure (some false)) (c + 243) := by
    intro answer
    let s := Riscv.writeHash (indexInputState image pk m bits) answer
    have sameCode : s.code = (indexInputState image pk m bits).code := by
      change (Riscv.writeHash _ _).code = _
      simp [Riscv.writeHash]
    have scratch : s.getReg .x19 = BitVec.ofNat 64 scratchBase := rfl
    have size : s.getReg .x13 = BitVec.ofNat 64 (min bits.length 5377) := rfl
    have index := indexOf_hash image pk m bits answer
    change indexOf s = (answer.setWidth 128).toNat at index
    have hr := indexChecks_refines s (fuel - 24) scratch
      (callLocated.tail.code_eq sameCode) (by omega) (q := q answer) (c := c) hc (fun hA hB => by
        rw [index] at hA
        rw [size, capped_length_eq] at hB
        exact continuation answer hA hB (fuel - 24 - 243) (by omega))
    refine hr.congr ?_
    simp only [index, size, capped_length_eq]
  have hashed := Riscv.Refines.hash (fuel := fuel - 24) callLocated.head
    (indexInput_registers image pk m bits).1 (indexInput_hashValid image pk m bits) afterHash
  rw [indexInput_hash image pk m bits hdata] at hashed
  have lin := Riscv.Refines.linear indexPrefix located.append_left ready hashed
  rw [length, show 23 + (fuel - 24 + 1) = fuel by omega] at lin
  refine lin.mono ?_
  change 23 + (blockCost paperParams 384 + (c + 243)) ≤ c + 267
  have : blockCost paperParams 384 = 1 := by decide
  omega

end OptimalOTS.RiscvUpperProgram
