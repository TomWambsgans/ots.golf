import Submissions.RiscvUpper.NodeReady
import Submissions.RiscvUpper.InitialStorage

/-! The immutable buffers and disclosure cursor of machine reconstruction. -/

namespace OptimalOTS.RiscvUpperProgram.Direct

open RiscvZkvm.Rv64 Forest Forest.Name RiscvUpperForest.ForestVerifier

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

/-- Stores in the node arena preserve all input and decoder memory below it. -/
def FrameBelow (s t : MachineState) : Prop :=
  ∀ addr : Word, addr.toNat < slotsBase → t.getMem addr = s.getMem addr

theorem FrameBelow.refl (s : MachineState) : FrameBelow s s := fun _ _ => rfl

theorem FrameBelow.trans {s t u : MachineState} (h : FrameBelow s t) (h' : FrameBelow t u) :
    FrameBelow s u := fun addr bound => (h' addr bound).trans (h addr bound)

theorem ExecutionContext.frame {s t : MachineState} {index : Idx paperParams}
    {payload : List Bool} {pk : PublicKey paperParams}
    (context : ExecutionContext s index payload pk) (frame : FrameBelow s t)
    (base : t.getReg .x8 = s.getReg .x8) : ExecutionContext t index payload pk := by
  refine ⟨base.trans context.positionBase, ?_, ?_, ?_⟩
  · intro k hk
    rw [base, frame]
    · exact context.positions k hk
    · rw [context.positionBase]
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat, positionsBase, slotsBase]
      omega
  · apply memBits_frame_interval s t _ _ (by decide) (by decide) context.payloadBits
    intro addr _ hi
    apply frame
    change addr.toNat < 4194368 + (5248 + 7) / 8 at hi
    unfold slotsBase
    omega
  · apply memBits_frame_interval s t _ _ (by decide) (by decide) context.publicKey
    intro addr _ hi
    apply frame
    change addr.toNat < 4194304 + (128 + 7) / 8 at hi
    unfold slotsBase
    omega

theorem ExecutionContext.setPC {s : MachineState} {index : Idx paperParams}
    {payload : List Bool} {pk : PublicKey paperParams}
    (context : ExecutionContext s index payload pk) (pc : Word) :
    ExecutionContext (s.setPC pc) index payload pk :=
  ⟨context.positionBase, context.positions, context.payloadBits, context.publicKey⟩

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

end OptimalOTS.RiscvUpperProgram.Direct
