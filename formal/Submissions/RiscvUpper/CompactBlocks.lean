import Submissions.RiscvUpper.CompactLayout
import Submissions.RiscvUpper.TagStore
import Submissions.RiscvUpper.Refines

/-!
# Machine semantics of the compact blocks

Generic lemmas for assembling concatenations in memory relative to an aligned base, the chain
slot addresses, and the registers fixed throughout the chain phase.
-/

namespace OptimalOTS.RiscvUpperProgram.Compact

open RiscvZkvm.Rv64 OracleComp

/-! ## Aligned bases -/

/-- The doubleword containing bit `i` of an aligned buffer. -/
theorem aligned_bit_word (base : Word) (aligned : base.toNat % 8 = 0) (i : ℕ)
    (small : base.toNat + i / 8 < 2 ^ 64) :
    alignToDword (base + BitVec.ofNat 64 (i / 8)) = base + BitVec.ofNat 64 (8 * (i / 64)) := by
  apply BitVec.eq_of_toNat_eq
  simp only [alignToDword_toNat, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem aligned_offset (base : Word) (aligned : base.toNat % 8 = 0) (off : ℕ) (hoff : off % 8 = 0)
    (small : base.toNat + off < 2 ^ 64) :
    alignToDword (base + BitVec.ofNat 64 off) = base + BitVec.ofNat 64 off := by
  apply (aligned_iff _).mpr
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem getReg_x0 (t : MachineState) : t.getReg .x0 = 0 := rfl

/-! ## Appending in a buffer at `x18 + off` -/

/-- The tag store after a complete word prefix leaves that prefix unchanged and supplies the
sixteen high bits. -/
theorem tag_append {width : ℕ} (s : MachineState) (off : ℕ) (value : BitVec width)
    (tag : BitVec 16) (bounded : width ≤ 896) (wordAligned : width % 64 = 0)
    (literal : (literalValue tag.toNat).truncate 16 = tag)
    (hoff : off + width / 8 < 2048) (offAligned : off % 8 = 0)
    (baseAligned : (s.getReg .x18).toNat % 8 = 0)
    (small : (s.getReg .x18).toNat + 2048 < 2 ^ 64)
    (represented : MemBits s (s.getReg .x18 + BitVec.ofNat 64 off) value) :
    MemBits ((writeTag tag (off + width / 8)).foldl execInstrBr s)
      (s.getReg .x18 + BitVec.ofNat 64 off) (tag ++ value) := by
  have base : (s.getReg .x18 + BitVec.ofNat 64 off).toNat = (s.getReg .x18).toNat + off := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega : off < 2 ^ 64), Nat.mod_eq_of_lt (by omega)]
  have tagAddr : s.getReg .x18 + BitVec.ofNat 64 (off + width / 8) =
      (s.getReg .x18 + BitVec.ofNat 64 off) + BitVec.ofNat 64 (width / 8) := by
    rw [BitVec.ofNat_add, BitVec.add_assoc]
  have alignedBase : (s.getReg .x18 + BitVec.ofNat 64 off).toNat % 8 = 0 := by rw [base]; omega
  apply memBits_append (by omega)
  · apply memBits_of_word_frame s _ _ value represented
    intro i hi
    apply writeTag_frame _ _ _ _ (by omega) literal
    rw [tagAddr, aligned_bit_word _ alignedBase i (by rw [base]; omega),
      aligned_offset _ alignedBase _ (by omega) (by rw [base]; omega)]
    exact add_offset_ne _ (by omega) (by omega) (by omega)
  · rw [← tagAddr]
    exact writeTag_memBits s tag _ (by omega) literal
      (aligned_offset _ baseAligned _ (by omega) (by omega))

/-- Copying a 128-bit word after a complete word prefix implements concatenation. -/
theorem copy_append {width : ℕ} (s : MachineState) (src : Reg) (srcOff off : ℕ)
    (lo : BitVec width) (hi : BitVec 128) (bounded : width ≤ 896) (wordAligned : width % 64 = 0)
    (hs : src ≠ .x26) (hsrc : srcOff + 8 < 2048) (hoff : off + width / 8 + 8 < 2048)
    (offAligned : off % 8 = 0)
    (baseAligned : (s.getReg .x18).toNat % 8 = 0)
    (small : (s.getReg .x18).toNat + 2048 < 2 ^ 64)
    (sourceAligned : alignToDword (s.getReg src + BitVec.ofNat 64 srcOff) =
      s.getReg src + BitVec.ofNat 64 srcOff)
    (preceding : MemBits s (s.getReg .x18 + BitVec.ofNat 64 off) lo)
    (source : MemBits s (s.getReg src + BitVec.ofNat 64 srcOff) hi) :
    MemBits ((copy128 src srcOff .x18 (off + width / 8)).foldl execInstrBr s)
      (s.getReg .x18 + BitVec.ofNat 64 off) (hi ++ lo) := by
  have base : (s.getReg .x18 + BitVec.ofNat 64 off).toNat = (s.getReg .x18).toNat + off := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega : off < 2 ^ 64), Nat.mod_eq_of_lt (by omega)]
  have dstAddr : s.getReg .x18 + BitVec.ofNat 64 (off + width / 8) =
      (s.getReg .x18 + BitVec.ofNat 64 off) + BitVec.ofNat 64 (width / 8) := by
    rw [BitVec.ofNat_add, BitVec.add_assoc]
  have alignedBase : (s.getReg .x18 + BitVec.ofNat 64 off).toNat % 8 = 0 := by rw [base]; omega
  apply memBits_append (by omega)
  · apply memBits_of_word_frame s _ _ lo preceding
    intro i hi
    rw [copy128_getMem _ _ _ _ _ hs (by decide) (by decide)]
    simp only [signExtend12_nonnegative _ (by omega : off + width / 8 + 8 < 2048),
      signExtend12_nonnegative _ (by omega : off + width / 8 < 2048),
      signExtend12_nonnegative _ (by omega : srcOff + 8 < 2048),
      signExtend12_nonnegative _ (by omega : srcOff < 2048)]
    rw [aligned_bit_word _ alignedBase i (by rw [base]; omega)]
    rw [if_neg, if_neg]
    · rw [dstAddr]
      exact add_offset_ne _ (by omega) (by omega) (by omega)
    · rw [show off + width / 8 + 8 = off + (width / 8 + 8) by omega, BitVec.ofNat_add,
        ← BitVec.add_assoc]
      exact add_offset_ne _ (by omega) (by omega) (by omega)
  · have moved := copy128_memBits s src .x18 srcOff (off + width / 8) hs (by decide) (by decide)
      hsrc (by omega) sourceAligned (aligned_offset _ baseAligned _ (by omega) (by omega)) hi source
    rw [dstAddr] at moved
    exact moved

/-! ## Chain slots -/

theorem constant_small (r : Reg) (p : ℕ) (hp : p < 2048) :
    constant r p = [.ADDI r .x0 (BitVec.ofNat 12 p)] := by
  simp [constant, hp]

def slotAddr (k : ℕ) : Word := BitVec.ofNat 64 chainsBase + BitVec.ofNat 64 (chainSlot k)

theorem slotAddr_word (k j : ℕ) :
    slotAddr k + BitVec.ofNat 64 (8 * j) = BitVec.ofNat 64 chainsBase + BitVec.ofNat 64 (chainSlot k + 8 * j) := by
  rw [slotAddr, BitVec.ofNat_add, BitVec.add_assoc]

theorem slotAddr_aligned (k : ℕ) (hk : k < 36) : alignToDword (slotAddr k) = slotAddr k := by
  apply (aligned_iff _).mpr
  simp only [slotAddr, chainsBase, chainSlot, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem slotAddr_toNat (k : ℕ) (hk : k < 36) : (slotAddr k).toNat = chainsBase + chainSlot k := by
  simp only [slotAddr, chainsBase, chainSlot, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- Registers fixed throughout the chain phase. -/
structure ChainRegs (s : MachineState) : Prop where
  base : s.getReg .x18 = BitVec.ofNat 64 chainsBase
  call : s.getReg .x5 = Riscv.hashCall
  length : s.getReg .x11 = 144

theorem chain_half_access (k : ℕ) (hk : k < 36) :
    isValidHalfwordAccess (BitVec.ofNat 64 chainsBase + BitVec.ofNat 64 (chainSlot k + 16)) = true := by
  simp only [isValidHalfwordAccess, isAligned2, isValidMemAddr, MEM_START, MEM_END,
    INPUT_MEM_START, INPUT_MEM_END, RAM_MEM_START, RAM_MEM_END, chainsBase, chainSlot,
    BitVec.toNat_add, BitVec.toNat_ofNat, Bool.and_eq_true, Bool.or_eq_true,
    decide_eq_true_eq, beq_iff_eq]
  omega

end OptimalOTS.RiscvUpperProgram.Compact
