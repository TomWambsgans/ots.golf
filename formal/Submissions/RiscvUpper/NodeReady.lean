import Submissions.RiscvUpper.NodeProgramProof

/-! Memory safety of the direct forest compiler. -/

namespace OptimalOTS.RiscvUpperProgram.Direct

open RiscvZkvm.Rv64 Forest Forest.Name RiscvUpperForest.ForestVerifier

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
    (cursor : s.getReg .x9 = BitVec.ofNat 64 (Riscv.signatureBase.toNat + 32 + 16 * k)) :
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

theorem clearSlot_ready (s : MachineState) (n : Name)
    (dest : s.getReg .x18 = BitVec.ofNat 64 (slotAddress n)) :
    Riscv.LinearReady s clearSlot := by
  suffices ∀ (js : List ℕ) (t : MachineState),
      (∀ j ∈ js, j < 16) → t.getReg .x18 = BitVec.ofNat 64 (slotAddress n) →
      Riscv.LinearReady t (js.map fun j => .SD .x18 .x0 (BitVec.ofNat 12 (8 * j))) by
    exact this _ s (by simp) dest
  intro js
  induction js with
  | nil => intros; trivial
  | cons j js ih =>
    intro t bounds reg
    refine ⟨rfl, ?_, ih _ (fun k hk => bounds k (by simp [hk])) ?_⟩
    · change isValidDwordAccess (t.getReg .x18 + signExtend12 (BitVec.ofNat 12 (8 * j))) = true
      rw [signExtend12_nonnegative _ (by have := bounds j (by simp); omega), reg]
      exact slot_access n j (bounds j (by simp))
    · simpa only [execInstrBr, MachineState.getReg_setPC, getReg_store] using reg

/-- Guards read only the fixed position array. -/
theorem guards_ready (s : MachineState) (n : Name)
    (positions : s.getReg .x8 = BitVec.ofNat 64 positionsBase) :
    Riscv.LinearReady s (guards n) := by
  have offset (k : Fin 63) := signExtend12_nonnegative (8 * k.val) (by omega)
  have small (t : Fin 14) : t.val < 2048 := by omega
  have small_succ (t : Fin 14) : t.val + 1 < 2048 := by omega
  cases n with
  | src k | ci k t | ch k t | cv k t =>
    simp only [guards]
    split_ifs <;>
      simp [constant, small, small_succ, Riscv.LinearReady, Riscv.linearInstruction,
        Riscv.memoryReady, positions, offset, positionsBase, MEM_START, MEM_END, INPUT_MEM_START,
        INPUT_MEM_END, RAM_MEM_START, RAM_MEM_END] <;> omega
  | gc j | gh j | gv j | ec l | eh l | ev l =>
    exact (constant_ready _ _ _).append (constant_ready _ _ _)
  | rc | rh => trivial

/-- Guard evaluation preserves the address registers. -/
theorem guards_register (s : MachineState) (n : Name) (r : Reg)
    (h24 : r ≠ .x24) (h25 : r ≠ .x25) (h26 : r ≠ .x26) (h27 : r ≠ .x27) :
    ((guards n).foldl execInstrBr s).getReg r = s.getReg r := by
  cases n <;> simp only [guards] <;> (try split_ifs) <;>
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, execInstrBr,
      MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ .x24 r _ h24.symm,
      MachineState.getReg_setReg_ne _ .x25 r _ h25.symm,
      MachineState.getReg_setReg_ne _ .x26 r _ h26.symm,
      constant_preserves _ .x24 r _ h24.symm, constant_preserves _ .x25 r _ h25.symm,
      constant_preserves _ .x27 r _ h27.symm]

theorem readDisclosure_ready (s : MachineState) (n : Name)
    (dest : s.getReg .x18 = BitVec.ofNat 64 (slotAddress n)) (cursor : CursorReady s) :
    Riscv.LinearReady s readDisclosure := by
  refine (copy128_ready s .x9 .x18 0 0 (by decide) (by decide) (by decide) ?_ ?_ ?_ ?_).append ?_
  · simpa only [signExtend12_nonnegative 0 (by decide)] using cursor_access s cursor 0 (by decide)
  · simpa only [signExtend12_nonnegative 8 (by decide)] using cursor_access s cursor 1 (by decide)
  · simpa only [signExtend12_nonnegative 0 (by decide), dest] using slot_access n 0 (by decide)
  · simpa only [signExtend12_nonnegative 8 (by decide), dest] using slot_access n 1 (by decide)
  · trivial

/-- Safe straight-line blocks preserve the destination slot pointer. -/
def SlotBlock (code : Code) : Prop :=
  ∀ (s : MachineState) (n : Name), s.getReg .x18 = BitVec.ofNat 64 (slotAddress n) →
    Riscv.LinearReady s code ∧
      (code.foldl execInstrBr s).getReg .x18 = BitVec.ofNat 64 (slotAddress n)

theorem SlotBlock.append {first last : Code} (hfirst : SlotBlock first)
    (hlast : SlotBlock last) : SlotBlock (first ++ last) := by
  intro s n dest
  obtain ⟨ready, reg⟩ := hfirst s n dest
  obtain ⟨readyLast, regLast⟩ := hlast _ n reg
  exact ⟨ready.append readyLast, by simpa only [List.foldl_append] using regLast⟩

theorem copyChild_slotBlock (child : Name) (off : ℕ) (aligned : off % 8 = 0)
    (small : off + 16 ≤ 128) : SlotBlock (copyChild child off) := by
  intro s n dest
  let prepared := (constant .x7 (slotAddress child)).foldl execInstrBr s
  have src : prepared.getReg .x7 = BitVec.ofNat 64 (slotAddress child) := by
    rw [constant_value _ _ _ (by decide), slotAddress_literal]
  have dst : prepared.getReg .x18 = BitVec.ofNat 64 (slotAddress n) := by
    rw [constant_preserves _ _ _ _ (by decide), dest]
  have offEq : off = 8 * (off / 8) := by omega
  have offSucc : off + 8 = 8 * (off / 8 + 1) := by omega
  constructor
  · apply (constant_ready _ _ _).append
    apply copy128_ready prepared .x7 .x18 0 off (by decide) (by decide) (by decide)
    · simpa only [signExtend12_nonnegative 0 (by decide), src] using slot_access child 0 (by decide)
    · simpa only [signExtend12_nonnegative 8 (by decide), src] using slot_access child 1 (by decide)
    · rw [signExtend12_nonnegative _ (by omega), dst, offEq]
      exact slot_access n (off / 8) (by omega)
    · rw [signExtend12_nonnegative _ (by omega), dst, offSucc]
      exact slot_access n (off / 8 + 1) (by omega)
  · simpa only [copyChild, List.foldl_append,
      copy128_reg _ .x7 .x18 .x18 0 off (by decide) (by decide)] using dst

theorem writeTag_slotBlock (tag : BitVec 16) (off : ℕ) (aligned : off % 2 = 0)
    (small : off < 128) : SlotBlock (writeTag tag off) := by
  intro s n dest
  have dst : ((constant .x26 tag.toNat).foldl execInstrBr s).getReg .x18 =
      BitVec.ofNat 64 (slotAddress n) := by
    rw [constant_preserves _ _ _ _ (by decide), dest]
  have access : isValidHalfwordAccess
      (BitVec.ofNat 64 (slotAddress n) + BitVec.ofNat 64 off) = true := by
    have bounds := slotAddress_bounds n
    have addressAligned := slotAddress_aligned n
    simp only [isValidHalfwordAccess, isAligned2, isValidMemAddr, MEM_START, MEM_END,
      INPUT_MEM_START, INPUT_MEM_END, RAM_MEM_START, RAM_MEM_END,
      BitVec.toNat_add, BitVec.toNat_ofNat, Bool.and_eq_true, Bool.or_eq_true,
      decide_eq_true_eq, beq_iff_eq]
    omega
  constructor
  · apply (constant_ready _ _ _).append
    refine ⟨rfl, ?_, trivial⟩
    change isValidHalfwordAccess (_ + signExtend12 (BitVec.ofNat 12 off)) = true
    rw [signExtend12_nonnegative _ (by omega), dst]
    exact access
  · simp only [writeTag, List.foldl_append, List.foldl_cons, List.foldl_nil,
      execInstrBr, MachineState.getReg_setPC]
    exact dst

theorem SlotBlock.flatMap {α : Type} (xs : List α) (f : α → Code)
    (ready : ∀ x ∈ xs, SlotBlock (f x)) : SlotBlock (xs.flatMap f) := by
  induction xs with
  | nil => intro s n dest; exact ⟨trivial, dest⟩
  | cons x xs ih =>
    exact (ready x (by simp)).append (ih (fun y hy => ready y (by simp [hy])))

/-- Every operation is safe at an allocated destination slot. -/
theorem operation_ready (s : MachineState) (n : Name) (op : NodeOp)
    (dest : s.getReg .x18 = BitVec.ofNat 64 (slotAddress n)) : OperationReady s op := by
  cases op with
  | zero => trivial
  | copy source => exact (copyChild_slotBlock source 0 (by decide) (by decide) s n dest).1
  | tagged1 tag source =>
    exact ((copyChild_slotBlock source 0 (by decide) (by decide)).append
      (writeTag_slotBlock tag 16 (by decide) (by decide)) s n dest).1
  | tagged3 tag a b c =>
    exact ((((copyChild_slotBlock c 0 (by decide) (by decide)).append
      (copyChild_slotBlock b 16 (by decide) (by decide))).append
      (copyChild_slotBlock a 32 (by decide) (by decide))).append
      (writeTag_slotBlock tag 48 (by decide) (by decide)) s n dest).1
  | tagged7 tag children =>
    exact ((SlotBlock.flatMap (List.finRange 7).reverse _ (fun l _ =>
      copyChild_slotBlock (children l) (16 * (6 - l.val)) (by omega) (by omega))).append
      (writeTag_slotBlock tag 112 (by decide) (by decide)) s n dest).1
  | hash source =>
    constructor
    · exact ((constant_ready _ _ _).append (constant_ready _ _ _)).append
        (by simp [Riscv.LinearReady, Riscv.linearInstruction, Riscv.memoryReady])
    · obtain ⟨input, size, output⟩ := hashSetup_registers s source
      have bounds := slotAddress_bounds source
      have lenBound := node_length_bound source
      have src : isValidOutputRange (BitVec.ofNat 64 (slotAddress source))
          (((BitVec.ofNat 64 source.len).toNat + 7) / 8) = true := by
        simp only [isValidOutputRange, MAX_OUTPUT_BYTES, MEM_START, MEM_END,
          INPUT_MEM_START, INPUT_MEM_END, RAM_MEM_START, RAM_MEM_END,
          BitVec.toNat_ofNat, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]
        omega
      simp only [Riscv.hashArgumentsValid, input, size, output, dest, src,
        Bool.true_and, Bool.and_eq_true]
      refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
      · have h := slot_access n 0 (by decide)
        change isValidDwordAccess (BitVec.ofNat 64 (slotAddress n) + 0) = true at h
        rw [show BitVec.ofNat 64 (slotAddress n) + 0 = BitVec.ofNat 64 (slotAddress n)
          from BitVec.add_zero _] at h
        exact h
      · exact slot_access n 1 (by decide)
      · exact slot_access n 2 (by decide)
      · exact slot_access n 3 (by decide)

private theorem setup_destination (s : MachineState) (n : Name) :
    ((constant .x18 (slotAddress n) ++ clearSlot ++ guards n).foldl execInstrBr s).getReg .x18 =
      BitVec.ofNat 64 (slotAddress n) := by
  simp only [List.foldl_append, guards_register _ _ .x18 (by decide) (by decide)
    (by decide) (by decide), clearSlot_registers, constant_value _ .x18 _ (by decide),
    slotAddress_literal]

private theorem setup_address (s : MachineState) (n : Name) (r : Reg)
    (h18 : r ≠ .x18) (h24 : r ≠ .x24) (h25 : r ≠ .x25)
    (h26 : r ≠ .x26) (h27 : r ≠ .x27) :
    ((constant .x18 (slotAddress n) ++ clearSlot ++ guards n).foldl execInstrBr s).getReg r =
      s.getReg r := by
  simp only [List.foldl_append, guards_register _ _ r h24 h25 h26 h27,
    clearSlot_registers, constant_preserves _ _ _ _ h18.symm]

/-- The prelude always leaves the current node's slot selected. -/
theorem nodePrelude_destination (s : MachineState) (n : Name) :
    ((nodePrelude n).eval s).getReg .x18 = BitVec.ofNat 64 (slotAddress n) := by
  let before := (constant .x18 (slotAddress n) ++ clearSlot ++ guards n).foldl execInstrBr s
  change (if PureBlock.passes false .x24 before then
      readDisclosure.foldl execInstrBr (PureBlock.branchState false .x24 readDisclosure.length before)
    else PureBlock.branchState false .x24 readDisclosure.length before).getReg .x18 = _
  by_cases passed : PureBlock.passes false .x24
      ((constant .x18 (slotAddress n) ++ clearSlot ++ guards n).foldl execInstrBr s)
  · rw [if_pos passed]
    simp only [readDisclosure, List.foldl_append, List.foldl_cons, List.foldl_nil,
      execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ .x9 .x18 _ (by decide),
      copy128_reg _ .x9 .x18 .x18 0 0 (by decide) (by decide),
      PureBlock.branchState, MachineState.getReg_setPC]
    exact setup_destination s n
  · rw [if_neg passed]
    simp only [PureBlock.branchState, MachineState.getReg_setPC]
    exact setup_destination s n

/-- Fixed positions and a valid disclosure cursor suffice for the entire node prelude. -/
theorem nodePrelude_ready (s : MachineState) (n : Name)
    (positions : s.getReg .x8 = BitVec.ofNat 64 positionsBase) (cursor : CursorReady s) :
    (nodePrelude n).Ready s := by
  let selected := (constant .x18 (slotAddress n)).foldl execInstrBr s
  have dest : selected.getReg .x18 = BitVec.ofNat 64 (slotAddress n) := by
    rw [constant_value _ _ _ (by decide), slotAddress_literal]
  have pos : (clearSlot.foldl execInstrBr selected).getReg .x8 =
      BitVec.ofNat 64 positionsBase := by
    rw [clearSlot_registers, constant_preserves _ _ _ _ (by decide), positions]
  refine ⟨((constant_ready _ _ _).append (clearSlot_ready selected n dest)).append
    (guards_ready _ n (by simpa only [List.foldl_append] using pos)), ?_⟩
  refine ⟨by decide, ?_⟩
  intro _
  apply readDisclosure_ready _ n
  · simp only [PureBlock.branchState, MachineState.getReg_setPC, PureBlock.eval,
      setup_destination]
  · simpa only [CursorReady, PureBlock.branchState, MachineState.getReg_setPC,
      PureBlock.eval, setup_address _ _ .x9 (by decide) (by decide) (by decide)
        (by decide) (by decide)] using cursor

/-- Every node's memory operations are valid under the fixed-array invariant. -/
theorem node_ready (s : MachineState) (n : Name)
    (positions : s.getReg .x8 = BitVec.ofNat 64 positionsBase) (cursor : CursorReady s) :
    NodeReady s n := by
  refine ⟨nodePrelude_ready s n positions cursor, fun _ => ?_⟩
  apply operation_ready _ n
  simpa only [MachineState.getReg_setPC] using nodePrelude_destination s n

end OptimalOTS.RiscvUpperProgram.Direct
