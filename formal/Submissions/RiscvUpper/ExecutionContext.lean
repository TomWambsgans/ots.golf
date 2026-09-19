import Submissions.RiscvUpper.TagStore
import Submissions.RiscvUpper.InitialStorage

/-!
# The reconstruction context

The immutable input buffers and decoded chain positions read by the chain and tree phases
(`ExecutionContext`), and the disclosure cursor `x9`, which stays word-aligned inside the
signature buffer (`CursorAt`, `CursorReady`), so that every load it makes is admitted.
-/

namespace OptimalOTS.RiscvUpperProgram

open RiscvZkvm.Rv64 Forest Forest.Name RiscvUpperForest.ForestVerifier

/-- The decoded positions are stored as natural 64-bit words. -/
def PositionMemory (s : MachineState) (positions : Fin 63 → Fin 15) : Prop :=
  ∀ k : Fin 63, k.val < 36 →
    s.getMem (s.getReg .x8 + BitVec.ofNat 64 (8 * k.val)) = BitVec.ofNat 64 (positions k).val

/-- Each aligned doubleword in the fixed position array is accessible. -/
theorem position_access (k : Fin 63) :
    isValidDwordAccess (BitVec.ofNat 64 positionsBase + BitVec.ofNat 64 (8 * k.val)) = true := by
  have hk := k.isLt
  simp only [isValidDwordAccess, isAligned8, isValidMemAddr, MEM_START, MEM_END,
    INPUT_MEM_START, INPUT_MEM_END, RAM_MEM_START, RAM_MEM_END, positionsBase,
    BitVec.toNat_add, BitVec.toNat_ofNat, Bool.and_eq_true, Bool.or_eq_true,
    decide_eq_true_eq, beq_iff_eq]
  omega

/-- The aligned disclosure cursor stays within the signature buffer, including its end. -/
def CursorReady (s : MachineState) : Prop :=
  Riscv.signatureBase.toNat ≤ (s.getReg .x9).toNat ∧
    (s.getReg .x9).toNat ≤ Riscv.signatureBase.toNat + 688 ∧
    (s.getReg .x9).toNat % 8 = 0

/-- Consuming at most forty-one disclosure words keeps the cursor in its allocated buffer. -/
theorem cursorReady_of_wordIndex (s : MachineState) (k : ℕ) (bound : k ≤ 41)
    (cursor : s.getReg .x9 = BitVec.ofNat 64 (Riscv.signatureBase.toNat + 16 + 16 * k)) :
    CursorReady s := by
  have base : Riscv.signatureBase.toNat = 4194352 := rfl
  simp only [CursorReady, cursor, base, BitVec.toNat_ofNat]
  omega

theorem cursor_access (s : MachineState) (ready : CursorReady s) (j : ℕ) (hj : j < 2) :
    isValidDwordAccess (s.getReg .x9 + BitVec.ofNat 64 (8 * j)) = true := by
  obtain ⟨lower, upper, aligned⟩ := ready
  change 4194352 ≤ (s.getReg .x9).toNat at lower
  change (s.getReg .x9).toNat ≤ 4194352 + 688 at upper
  simp only [isValidDwordAccess, isAligned8, isValidMemAddr, MEM_START, MEM_END,
    INPUT_MEM_START, INPUT_MEM_END, RAM_MEM_START, RAM_MEM_END,
    BitVec.toNat_add, BitVec.toNat_ofNat, Bool.and_eq_true, Bool.or_eq_true,
    decide_eq_true_eq, beq_iff_eq]
  omega

/-- The immutable input buffers and decoded chain positions used by reconstruction. -/
structure ExecutionContext (s : MachineState) (index : Idx paperParams)
    (payload : List Bool) (pk : PublicKey paperParams) : Prop where
  positionBase : s.getReg .x8 = BitVec.ofNat 64 positionsBase
  positions : PositionMemory s (fixedPositions index)
  payloadBits : MemBits s (Riscv.signatureBase + 16) (ofBits 5248 payload)
  publicKey : MemBits s Riscv.publicKeyBase pk

/-- The bit cursor names the next complete signature word. -/
def CursorAt (s : MachineState) (cursor : ℕ) : Prop :=
  s.getReg .x9 = Riscv.signatureBase + 16 + BitVec.ofNat 64 (cursor / 8)

theorem CursorAt.ready {s : MachineState} {cursor : ℕ}
    (atCursor : CursorAt s cursor) (bounded : cursor ≤ 5248) (aligned : cursor % 128 = 0) :
    CursorReady s := by
  apply cursorReady_of_wordIndex s (cursor / 128) (by omega)
  rw [atCursor]
  rw [show cursor / 8 = 16 * (cursor / 128) by omega]
  simp only [BitVec.ofNat_add]
  rfl

/-- A disclosed word is read from the same bit offset as the specification. -/
theorem ExecutionContext.payload_word {s : MachineState} {index : Idx paperParams}
    {payload : List Bool} {pk : PublicKey paperParams}
    (context : ExecutionContext s index payload pk) (cursor : ℕ)
    (atCursor : CursorAt s cursor) (aligned : cursor % 128 = 0)
    (bounded : cursor + 128 ≤ 5248) :
    MemBits s (s.getReg .x9) (ofBits 128 (payload.drop cursor)) := by
  have h := memBits_extract (start := cursor) (len := 128) context.payloadBits
    (by omega) bounded
  rw [ofBits_extract payload bounded] at h
  rw [atCursor]
  exact h

end OptimalOTS.RiscvUpperProgram
