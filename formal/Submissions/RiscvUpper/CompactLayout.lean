import Submissions.RiscvUpper.CompactProgram
import Submissions.RiscvUpper.ExecutionContext

/-! Memory layout of the compact image: the arrays lie in admitted memory above every input. -/

namespace OptimalOTS.RiscvUpperProgram.Compact

open RiscvZkvm.Rv64

/-- Every doubleword of every chain slot is accessible. -/
theorem chain_access (k j : ℕ) (hk : k < 36) (hj : j < 4) :
    isValidDwordAccess (BitVec.ofNat 64 chainsBase + BitVec.ofNat 64 (chainSlot k + 8 * j)) =
      true := by
  simp only [isValidDwordAccess, isAligned8, isValidMemAddr, MEM_START, MEM_END,
    INPUT_MEM_START, INPUT_MEM_END, RAM_MEM_START, RAM_MEM_END, chainsBase, chainSlot,
    BitVec.toNat_add, BitVec.toNat_ofNat, Bool.and_eq_true, Bool.or_eq_true,
    decide_eq_true_eq, beq_iff_eq]
  omega

theorem group_access (j i : ℕ) (hj : j < 15) (hi : i < 4) :
    isValidDwordAccess (BitVec.ofNat 64 groupsBase + BitVec.ofNat 64 (groupSlot j + 8 * i)) =
      true := by
  simp only [isValidDwordAccess, isAligned8, isValidMemAddr, MEM_START, MEM_END,
    INPUT_MEM_START, INPUT_MEM_END, RAM_MEM_START, RAM_MEM_END, groupsBase, groupSlot,
    BitVec.toNat_add, BitVec.toNat_ofNat, Bool.and_eq_true, Bool.or_eq_true,
    decide_eq_true_eq, beq_iff_eq]
  omega

theorem subtree_access (l i : ℕ) (hl : l < 7) (hi : i < 4) :
    isValidDwordAccess (BitVec.ofNat 64 subtreesBase + BitVec.ofNat 64 (subtreeSlot l + 8 * i)) =
      true := by
  simp only [isValidDwordAccess, isAligned8, isValidMemAddr, MEM_START, MEM_END,
    INPUT_MEM_START, INPUT_MEM_END, RAM_MEM_START, RAM_MEM_END, subtreesBase, subtreeSlot,
    BitVec.toNat_add, BitVec.toNat_ofNat, Bool.and_eq_true, Bool.or_eq_true,
    decide_eq_true_eq, beq_iff_eq]
  omega

theorem scratch_access (i : ℕ) (hi : i < 20) :
    isValidDwordAccess (BitVec.ofNat 64 scratchBase + BitVec.ofNat 64 (8 * i)) = true := by
  simp only [isValidDwordAccess, isAligned8, isValidMemAddr, MEM_START, MEM_END,
    INPUT_MEM_START, INPUT_MEM_END, RAM_MEM_START, RAM_MEM_END, scratchBase,
    BitVec.toNat_add, BitVec.toNat_ofNat, Bool.and_eq_true, Bool.or_eq_true,
    decide_eq_true_eq, beq_iff_eq]
  omega

/-- Every chain hash input (18 bytes) is a valid output range. -/
theorem chain_output_range (k : Fin 36) :
    isValidOutputRange (BitVec.ofNat 64 chainsBase + BitVec.ofNat 64 (chainSlot k.val)) 18 =
      true := by
  revert k
  decide +kernel

theorem scratch_output_range_50 : isValidOutputRange (BitVec.ofNat 64 scratchBase) 50 = true := by
  decide +kernel

theorem scratch_output_range_114 : isValidOutputRange (BitVec.ofNat 64 scratchBase) 114 = true := by
  decide +kernel

/-- Machine words below the chain array: every input buffer and the decoded positions. -/
def FrameInputs (s t : MachineState) : Prop :=
  ∀ addr : Word, addr.toNat < chainsBase → t.getMem addr = s.getMem addr

/-- The reconstruction context survives any writes at or above the chain array. -/
theorem _root_.OptimalOTS.RiscvUpperProgram.ExecutionContext.frameInputs {s t : MachineState} {index : Idx paperParams}
    {payload : List Bool} {pk : PublicKey paperParams}
    (context : ExecutionContext s index payload pk) (frame : FrameInputs s t)
    (base : t.getReg .x8 = s.getReg .x8) : ExecutionContext t index payload pk := by
  refine ⟨base.trans context.positionBase, ?_, ?_, ?_⟩
  · intro k hk
    rw [base, frame]
    · exact context.positions k hk
    · rw [context.positionBase]
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat, positionsBase, chainsBase]
      omega
  · apply memBits_frame_interval s t _ _ (by decide) (by decide) context.payloadBits
    intro addr _ hi
    apply frame
    change addr.toNat < 4194368 + (5248 + 7) / 8 at hi
    unfold chainsBase
    omega
  · apply memBits_frame_interval s t _ _ (by decide) (by decide) context.publicKey
    intro addr _ hi
    apply frame
    change addr.toNat < 4194304 + (128 + 7) / 8 at hi
    unfold chainsBase
    omega

end OptimalOTS.RiscvUpperProgram.Compact
