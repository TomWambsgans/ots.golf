import Submissions.RiscvUpper.IndexChecks

/-! The complete initial query and wire-format checks, with a verified continuation. -/

namespace OptimalOTS.RiscvUpperProgram

open RiscvZkvm.Rv64 OracleComp

theorem indexAndChecks_parts : indexAndChecks = indexPrefix ++ .ECALL :: indexChecks := by
  decide +kernel

theorem indexAndChecks_length : indexAndChecks.length = 42 := by decide +kernel

/-- The machine issues the specified first query, rejects exactly the invalid index/length
cases, and otherwise enters any proved continuation. -/
theorem indexAndChecks_continuation (image : Riscv.Image) (pk : PublicKey paperParams)
    (m : Message paperParams) (bits : List Bool) (hdata : image.data.length ≤ 1048576)
    (rest fuel : ℕ) (q : BitVec 256 → OracleComp (Spec paperParams) (Option Bool))
    (located : Riscv.CodeAt (Riscv.initialState image pk m bits)
      (Riscv.initialState image pk m bits).pc indexAndChecks)
    (bound : indexAndChecks.length + rest ≤ fuel)
    (continuation : ∀ answer, (answer.setWidth 128).toNat < 2 ^ 115 → bits.length = 5504 →
      ∀ left, rest ≤ left →
        Riscv.observe left
          (checkedIndexState (Riscv.writeHash (indexInputState image pk m bits) answer)) = q answer) :
    Riscv.observe fuel (Riscv.initialState image pk m bits) = (do
      let answer ← hash paperParams (m ++ ofBits 256 bits)
      if (answer.setWidth 128).toNat < 2 ^ 115 ∧ bits.length = 5504 then q answer
      else pure (some false)) := by
  rw [indexAndChecks_parts] at located
  have ready := indexPrefix_ready image pk m bits
  have callLocated : Riscv.CodeAt (indexInputState image pk m bits)
      (indexInputState image pk m bits).pc (.ECALL :: indexChecks) := by
    change Riscv.CodeAt (indexInputState image pk m bits)
      (indexPrefix.foldl execInstrBr (Riscv.initialState image pk m bits)).pc _
    rw [Riscv.linear_fold_pc _ _ ready]
    exact located.append_right.code_eq (Riscv.fold_code _ _)
  have length := indexPrefix_length
  have enough : 42 + rest ≤ fuel := by simpa only [indexAndChecks_length] using bound
  rw [show fuel = indexPrefix.length + (fuel - 27) by omega,
    Riscv.observe_linear _ _ _ located.append_left ready]
  change Riscv.observe (fuel - 27) (indexInputState image pk m bits) = _
  rw [show fuel - 27 = (fuel - 28) + 1 by omega,
    Riscv.observe_hash _ _ callLocated.head (indexInput_registers image pk m bits).1
      (indexInput_hashValid image pk m bits), indexInput_hash image pk m bits hdata]
  apply congrArg (fun f => hash paperParams (m ++ ofBits 256 bits) >>= f)
  funext answer
  apply indexChecks_continuation image pk m bits answer rest (fuel - 28) (q answer)
  · exact callLocated.tail.code_eq (by simp [Riscv.writeHash])
  · rw [indexChecks_length]
    omega
  · exact continuation answer

end OptimalOTS.RiscvUpperProgram
