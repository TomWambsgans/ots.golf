import Submissions.RiscvUpper.CompactLayout
import Submissions.RiscvUpper.NodeRefinement
import Submissions.RiscvUpper.Refines

/-!
# Machine semantics of the compact blocks

Generic lemmas for assembling concatenations in memory relative to an aligned base, then the
exact effect of the guarded read block and of the guarded chain hash block.
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

theorem ofNat_eq_iff (a b : ℕ) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    BitVec.ofNat 64 a = BitVec.ofNat 64 b ↔ a = b := by
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat] at this
    rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this
  · intro h
    rw [h]

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
    MemBits ((Direct.writeTag tag (off + width / 8)).foldl execInstrBr s)
      (s.getReg .x18 + BitVec.ofNat 64 off) (tag ++ value) := by
  have base : (s.getReg .x18 + BitVec.ofNat 64 off).toNat = (s.getReg .x18).toNat + off := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega : off < 2 ^ 64), Nat.mod_eq_of_lt (by omega)]
  have tagAddr : s.getReg .x18 + BitVec.ofNat 64 (off + width / 8) =
      (s.getReg .x18 + BitVec.ofNat 64 off) + BitVec.ofNat 64 (width / 8) := by
    rw [BitVec.ofNat_add, BitVec.add_assoc]
  have alignedBase : (s.getReg .x18 + BitVec.ofNat 64 off).toNat % 8 = 0 := by rw [base]; omega
  apply memBits_append (by omega)
  · apply Direct.memBits_of_word_frame s _ _ value represented
    intro i hi
    apply Direct.writeTag_frame _ _ _ _ (by omega) literal
    rw [tagAddr, aligned_bit_word _ alignedBase i (by rw [base]; omega),
      aligned_offset _ alignedBase _ (by omega) (by rw [base]; omega)]
    exact add_offset_ne _ (by omega) (by omega) (by omega)
  · rw [← tagAddr]
    exact Direct.writeTag_memBits s tag _ (by omega) literal
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
  · apply Direct.memBits_of_word_frame s _ _ lo preceding
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

/-! ## The guarded read block -/

def readPrefix (p k : ℕ) : Code :=
  [.LD .x26 .x8 (BitVec.ofNat 12 (8 * k))] ++ constant .x27 p ++ [.XOR .x26 .x26 .x27]

def readBody (k : ℕ) : Code := copy128 .x9 0 .x18 (chainSlot k) ++ [.ADDI .x9 .x9 16]

def readBlock (p k : ℕ) : PureBlock :=
  .seq (.linear (readPrefix p k)) (.guard true .x26 (.linear (readBody k)))

theorem readBlock_code (p k : ℕ) : (readBlock p k).code = readChain p k := by
  simp only [readBlock, PureBlock.code, readChain, readPrefix, readBody, whenZero,
    List.append_assoc, if_true, ite_true]

theorem constant_small (r : Reg) (p : ℕ) (hp : p < 2048) :
    constant r p = [.ADDI r .x0 (BitVec.ofNat 12 p)] := by
  simp [constant, hp]

/-- The prefix loads and compares the position; it changes only its two temporaries. -/
theorem readPrefix_effect (s : MachineState) (p k : ℕ) (hp : p < 2048) (hk : k < 63) :
    ((readPrefix p k).foldl execInstrBr s).getReg .x26 =
        s.getMem (s.getReg .x8 + BitVec.ofNat 64 (8 * k)) ^^^ BitVec.ofNat 64 p ∧
    (∀ r, r ≠ .x26 → r ≠ .x27 →
      ((readPrefix p k).foldl execInstrBr s).getReg r = s.getReg r) ∧
    ((readPrefix p k).foldl execInstrBr s).mem = s.mem := by
  have unfolded : (readPrefix p k).foldl execInstrBr s =
      execInstrBr (execInstrBr (execInstrBr s (.LD .x26 .x8 (BitVec.ofNat 12 (8 * k))))
        (.ADDI .x27 .x0 (BitVec.ofNat 12 p))) (.XOR .x26 .x26 .x27) := by
    simp [readPrefix, constant_small _ _ hp]
  rw [unfolded]
  simp only [execInstrBr, signExtend12_nonnegative _ (by omega : 8 * k < 2048),
    signExtend12_nonnegative _ hp]
  refine ⟨?_, ?_, ?_⟩
  · simp only [MachineState.getReg_setPC, MachineState.getReg_setReg_eq (by decide : Reg.x26 ≠ .x0),
      MachineState.getReg_setReg_eq (by decide : Reg.x27 ≠ .x0),
      MachineState.getReg_setReg_ne _ .x27 .x26 _ (by decide),
      MachineState.getMem_setReg, getReg_x0]
    simp
  · intro r h26 h27
    simp only [MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ .x26 r _ h26.symm,
      MachineState.getReg_setReg_ne _ .x27 r _ h27.symm]
  · rfl

theorem readPrefix_ready (s : MachineState) (p k : ℕ) (hp : p < 2048) (hk : k < 63)
    (base : s.getReg .x8 = BitVec.ofNat 64 positionsBase) :
    Riscv.LinearReady s (readPrefix p k) := by
  simp only [readPrefix, constant_small _ _ hp, List.append_assoc, List.singleton_append]
  refine ⟨rfl, ?_, rfl, trivial, rfl, trivial, trivial⟩
  change isValidDwordAccess (s.getReg .x8 + signExtend12 (BitVec.ofNat 12 (8 * k))) = true
  rw [signExtend12_nonnegative _ (by omega), base]
  exact Direct.position_access ⟨k, hk⟩

theorem readPrefix_length (p k : ℕ) (hp : p < 2048) : (readPrefix p k).length = 3 := by
  simp [readPrefix, constant_small _ _ hp]

/-- The body copies the next disclosed word into the slot and advances the cursor. -/
theorem readBody_effect (s : MachineState) (k : ℕ) (hk : k < 36) :
    ((readBody k).foldl execInstrBr s).getReg .x9 = s.getReg .x9 + 16 ∧
    (∀ r, r ≠ .x9 → r ≠ .x26 → r ≠ .x27 →
      ((readBody k).foldl execInstrBr s).getReg r = s.getReg r) ∧
    ((readBody k).foldl execInstrBr s).mem =
      ((copy128 .x9 0 .x18 (chainSlot k)).foldl execInstrBr s).mem := by
  have h16 : signExtend12 (16 : BitVec 12) = (16 : Word) := by decide
  simp only [readBody, List.foldl_append, List.foldl_cons, List.foldl_nil, execInstrBr, h16]
  refine ⟨?_, ?_, rfl⟩
  · simp only [MachineState.getReg_setPC, MachineState.getReg_setReg_eq (by decide : Reg.x9 ≠ .x0),
      copy128_reg _ .x9 .x18 .x9 0 _ (by decide) (by decide)]
  · intro r h9 h26 h27
    simp only [MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ .x9 r _ h9.symm,
      copy128_reg _ .x9 .x18 r 0 _ h26 h27]

theorem readBody_ready (s : MachineState) (k : ℕ) (hk : k < 36)
    (base : s.getReg .x18 = BitVec.ofNat 64 chainsBase) (cursor : Direct.CursorReady s) :
    Riscv.LinearReady s (readBody k) := by
  refine (copy128_ready s .x9 .x18 0 (chainSlot k) (by decide) (by decide) (by decide)
    ?_ ?_ ?_ ?_).append ?_
  · simpa only [signExtend12_nonnegative 0 (by decide)] using
      Direct.cursor_access s cursor 0 (by decide)
  · simpa only [signExtend12_nonnegative 8 (by decide)] using
      Direct.cursor_access s cursor 1 (by decide)
  · rw [signExtend12_nonnegative _ (by unfold chainSlot; omega), base]
    simpa only [Nat.mul_zero, Nat.add_zero] using chain_access k 0 hk (by decide)
  · rw [signExtend12_nonnegative _ (by unfold chainSlot; omega), base]
    simpa only [Nat.mul_one] using chain_access k 1 hk (by decide)
  · exact ⟨rfl, trivial, trivial⟩

theorem readBody_length (k : ℕ) : (readBody k).length = 5 := rfl


/-! ## The guarded chain hash block -/

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

def hashPrefix (t k : ℕ) : Code :=
  [.LD .x26 .x8 (BitVec.ofNat 12 (8 * k)), .SLTIU .x26 .x26 (BitVec.ofNat 12 (t + 1))]

def hashBody (t k : ℕ) : Code :=
  Direct.writeTag (BitVec.ofNat 16 (126 + 189 * t + k)) (chainSlot k + 16) ++
  [.ADDI .x10 .x18 (BitVec.ofNat 12 (chainSlot k)), .ADDI .x12 .x18 (BitVec.ofNat 12 (chainSlot k))]

theorem hashChain_parts (t k : ℕ) :
    hashChain t k = hashPrefix t k ++ whenNonzero .x26 (hashBody t k ++ [.ECALL]) := by
  simp [hashChain, hashPrefix, hashBody, List.append_assoc]

theorem hashBody_length (t k : ℕ) : (hashBody t k).length = (Direct.writeTag (BitVec.ofNat 16 (126 + 189 * t + k)) (chainSlot k + 16)).length + 2 := by
  simp [hashBody]

theorem hashChain_length (t k : ℕ) :
    (hashChain t k).length = 2 + 1 + ((hashBody t k).length + 1) := by
  rw [hashChain_parts]
  simp [hashPrefix, whenNonzero]
  omega

/-- The prefix computes the evaluation flag and changes only `x26`. -/
theorem hashPrefix_effect (s : MachineState) (t k : ℕ) (ht : t + 1 < 2048) (hk : k < 63) :
    ((hashPrefix t k).foldl execInstrBr s).getReg .x26 =
        (if BitVec.ult (s.getMem (s.getReg .x8 + BitVec.ofNat 64 (8 * k))) (BitVec.ofNat 64 (t + 1))
          then 1 else 0) ∧
    (∀ r, r ≠ .x26 → ((hashPrefix t k).foldl execInstrBr s).getReg r = s.getReg r) ∧
    ((hashPrefix t k).foldl execInstrBr s).mem = s.mem := by
  simp only [hashPrefix, List.foldl_cons, List.foldl_nil, execInstrBr,
    signExtend12_nonnegative _ (by omega : 8 * k < 2048), signExtend12_nonnegative _ ht]
  refine ⟨?_, ?_, rfl⟩
  · simp only [MachineState.getReg_setPC, MachineState.getReg_setReg_eq (by decide : Reg.x26 ≠ .x0),
      MachineState.getMem_setPC, MachineState.getMem_setReg]
  · intro r h26
    simp only [MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ .x26 r _ h26.symm]

theorem hashPrefix_ready (s : MachineState) (t k : ℕ) (hk : k < 63)
    (base : s.getReg .x8 = BitVec.ofNat 64 positionsBase) :
    Riscv.LinearReady s (hashPrefix t k) := by
  refine ⟨rfl, ?_, rfl, trivial, trivial⟩
  change isValidDwordAccess (s.getReg .x8 + signExtend12 (BitVec.ofNat 12 (8 * k))) = true
  rw [signExtend12_nonnegative _ (by omega), base]
  exact Direct.position_access ⟨k, hk⟩

/-- Small positions compare as naturals. -/
theorem ult_small (a b : ℕ) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    BitVec.ult (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) = decide (a < b) := by
  simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

theorem chain_half_access (k : ℕ) (hk : k < 36) :
    isValidHalfwordAccess (BitVec.ofNat 64 chainsBase + BitVec.ofNat 64 (chainSlot k + 16)) = true := by
  simp only [isValidHalfwordAccess, isAligned2, isValidMemAddr, MEM_START, MEM_END,
    INPUT_MEM_START, INPUT_MEM_END, RAM_MEM_START, RAM_MEM_END, chainsBase, chainSlot,
    BitVec.toNat_add, BitVec.toNat_ofNat, Bool.and_eq_true, Bool.or_eq_true,
    decide_eq_true_eq, beq_iff_eq]
  omega

theorem chainTag_literal (t : Fin 14) (k : Fin 63) :
    (literalValue (BitVec.ofNat 16 (126 + 189 * t.val + k.val)).toNat).truncate 16 =
      BitVec.ofNat 16 (126 + 189 * t.val + k.val) :=
  Direct.nodeTag_literal (.ch k t)

/-- The body writes the tag after the value and points both hash pointers at the slot. -/
theorem hashBody_effect (s : MachineState) (t : Fin 14) (k : Fin 63) (hk : k.val < 36) :
    ((hashBody t k).foldl execInstrBr s).getReg .x10 = s.getReg .x18 + BitVec.ofNat 64 (chainSlot k) ∧
    ((hashBody t k).foldl execInstrBr s).getReg .x12 = s.getReg .x18 + BitVec.ofNat 64 (chainSlot k) ∧
    (∀ r, r ≠ .x10 → r ≠ .x12 → r ≠ .x26 →
      ((hashBody t k).foldl execInstrBr s).getReg r = s.getReg r) ∧
    ((hashBody t k).foldl execInstrBr s).mem =
      (s.setHalfword (s.getReg .x18 + BitVec.ofNat 64 (chainSlot k + 16))
        (BitVec.ofNat 16 (126 + 189 * t.val + k.val))).mem := by
  have hslot : chainSlot k < 2048 := by unfold chainSlot; omega
  simp only [hashBody, List.foldl_append, List.foldl_cons, List.foldl_nil, execInstrBr,
    signExtend12_nonnegative _ hslot]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ .x12 .x10 _ (by decide),
      MachineState.getReg_setReg_eq (by decide : Reg.x10 ≠ .x0),
      MachineState.getReg_setReg_ne _ .x10 .x18 _ (by decide),
      Direct.writeTag_register _ _ _ .x18 (by decide)]
  · simp only [MachineState.getReg_setPC, MachineState.getReg_setReg_eq (by decide : Reg.x12 ≠ .x0),
      MachineState.getReg_setReg_ne _ .x10 .x18 _ (by decide),
      Direct.writeTag_register _ _ _ .x18 (by decide)]
  · intro r h10 h12 h26
    simp only [MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ .x12 r _ h12.symm,
      MachineState.getReg_setReg_ne _ .x10 r _ h10.symm, Direct.writeTag_register _ _ _ r h26]
  · simp only [MachineState.setPC, MachineState.setReg]
    exact Direct.writeTag_memory s _ _ (by unfold chainSlot; omega) (chainTag_literal t k)

theorem hashBody_ready (s : MachineState) (t : Fin 14) (k : Fin 63) (hk : k.val < 36)
    (base : s.getReg .x18 = BitVec.ofNat 64 chainsBase) :
    Riscv.LinearReady s (hashBody t k) := by
  refine Riscv.LinearReady.append ?_ ⟨rfl, trivial, rfl, trivial, trivial⟩
  apply (constant_ready _ _ _).append
  refine ⟨rfl, ?_, trivial⟩
  change isValidHalfwordAccess (_ + signExtend12 (BitVec.ofNat 12 (chainSlot k + 16))) = true
  rw [signExtend12_nonnegative _ (by unfold chainSlot; omega),
    constant_preserves _ .x26 .x18 _ (by decide), base]
  exact chain_half_access k hk

end OptimalOTS.RiscvUpperProgram.Compact
