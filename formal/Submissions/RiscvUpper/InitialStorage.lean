import Submissions.RiscvUpper.IndexChecks
import Submissions.RiscvUpper.ForestVerifier

/-! Input buffers survive the index query and the nibble checks. -/

namespace OptimalOTS.RiscvUpperProgram

open RiscvZkvm.Rv64

/-- Preserving aligned words in a byte interval preserves the represented vector. -/
theorem memBits_frame_interval {width : ℕ} (s t : MachineState) (base : Word)
    (value : BitVec width) (aligned : base.toNat % 8 = 0)
    (bounded : base.toNat + (width + 7) / 8 < 2 ^ 64)
    (represented : MemBits s base value)
    (frame : ∀ addr, base.toNat ≤ addr.toNat → addr.toNat < base.toNat + (width + 7) / 8 →
      t.getMem addr = s.getMem addr) : MemBits t base value := by
  intro i hi
  have ha : (base + BitVec.ofNat 64 (i / 8)).toNat = base.toNat + i / 8 := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega : i / 8 < 2 ^ 64), Nat.mod_eq_of_lt (by omega)]
  have address := alignToDword_toNat (base + BitVec.ofNat 64 (i / 8))
  rw [ha] at address
  have same := frame (alignToDword (base + BitVec.ofNat 64 (i / 8))) (by omega) (by omega)
  simp only [MachineState.getByte, same]
  exact represented i hi

/-- The index query changes only its scratch input and output interval. -/
theorem indexHash_frame (image : Riscv.Image) (pk : PublicKey paperParams)
    (m : Message paperParams) (bits : List Bool) (answer : BitVec 256) (addr : Word)
    (outside : addr.toNat < scratchBase ∨ scratchBase + 160 ≤ addr.toNat) :
    (Riscv.writeHash (indexInputState image pk m bits) answer).getMem addr =
      (Riscv.initialState image pk m bits).getMem addr := by
  rw [writeHash_frame, indexInput_frame_interval]
  · rcases outside with h | h
    · exact Or.inl h
    · exact Or.inr (by omega)
  · intro j hj heq
    rw [(indexInput_registers image pk m bits).2.2.2.1] at heq
    have h := congrArg BitVec.toNat heq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at h
    norm_num only [scratchBase, Nat.reduceAdd, Nat.reducePow] at h outside
    omega

/-- The nibble checks preserve a represented vector outside the position array. -/
theorem checked_memBits (s : MachineState) {width : ℕ} (base : Word) (value : BitVec width)
    (aligned : base.toNat % 8 = 0) (bounded : base.toNat + (width + 7) / 8 < 2 ^ 64)
    (outside : base.toNat + (width + 7) / 8 ≤ positionsBase ∨
      positionsBase + 288 ≤ base.toNat) (represented : MemBits s base value) :
    MemBits (checkedIndexState s) base value := by
  apply memBits_frame_interval s _ base value aligned bounded represented
  intro addr lo hi
  apply checked_frame s addr
  omega

/-- The index query preserves the transmitted public key. -/
theorem indexHash_publicKey (image : Riscv.Image) (pk : PublicKey paperParams)
    (m : Message paperParams) (bits : List Bool) (answer : BitVec 256) :
    MemBits (Riscv.writeHash (indexInputState image pk m bits) answer) Riscv.publicKeyBase pk := by
  apply memBits_frame_interval (Riscv.initialState image pk m bits) _ _ _ (by decide)
    (by decide) (initialState_publicKey image pk m bits)
  intro addr lo hi
  apply indexHash_frame
  left
  change addr.toNat < 4194304 + (128 + 7) / 8 at hi
  unfold scratchBase
  omega

/-- The index query preserves all 41 transmitted disclosure words. -/
theorem indexHash_payload (image : Riscv.Image) (pk : PublicKey paperParams)
    (m : Message paperParams) (bits : List Bool) (answer : BitVec 256)
    (hdata : image.data.length ≤ 1048576) :
    MemBits (Riscv.writeHash (indexInputState image pk m bits) answer)
      (Riscv.signatureBase + 16) (ofBits 5248 (bits.drop 128)) := by
  have payload := memBits_extract (start := 128) (len := 5248)
    (initialState_signature image pk m bits hdata) (by decide) (by decide)
  rw [ofBits_extract _ (by decide), ofBits_drop_take _ (by decide)] at payload
  apply memBits_frame_interval (Riscv.initialState image pk m bits) _ _ _ (by decide)
    (by decide) payload
  intro addr lo hi
  apply indexHash_frame
  left
  change addr.toNat < 4194368 + (5248 + 7) / 8 at hi
  unfold scratchBase
  omega

end OptimalOTS.RiscvUpperProgram
