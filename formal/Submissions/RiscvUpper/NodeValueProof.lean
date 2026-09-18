import Submissions.RiscvUpper.NodeRefinement

/-! Operation outputs and frames for the direct forest interpreter. -/

set_option maxRecDepth 4000
set_option maxHeartbeats 1000000

namespace OptimalOTS.RiscvUpperProgram.Direct

open RiscvZkvm.Rv64 Forest Forest.Name RiscvUpperForest.ForestVerifier OracleComp

set_option allowUnsafeReducibility true
attribute [local reducible] Forest.graph

/-- Width casts do not alter represented bits. -/
theorem memBits_cast {a b : ℕ} (s : MachineState) (base : Word) (v : BitVec a) (equal : a = b) :
    MemBits s base (v.cast equal) ↔ MemBits s base v := by
  subst equal
  rfl

/-- The machine stores the complete hash value at the destination slot. -/
theorem hashResult_value (s : MachineState) (dest source : Name) (v : BitVec (graph.len dest.fin))
    (length : graph.len dest.fin = 256)
    (destination : s.getReg .x18 = BitVec.ofNat 64 (slotAddress dest)) :
    MemBits (Riscv.writeHash ((hashSetup source).foldl execInstrBr s) (v.setWidth 256))
      (BitVec.ofNat 64 (slotAddress dest)) v := by
  have regs := hashSetup_registers s source
  have represented := writeHash_memBits ((hashSetup source).foldl execInstrBr s) (v.setWidth 256)
    (by rw [regs.2.2, destination]; exact slot_aligned dest)
  rw [regs.2.2, destination] at represented
  have same : v.setWidth 256 = v.cast length := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_cast, hi, decide_true, Bool.true_and]
  apply (memBits_cast _ _ v length).mp
  rw [← same]
  exact represented

/-- The resulting slot represents exactly the value returned by the certified node. -/
theorem nodeResult_value (s : MachineState) (n : Name) (x : graph.Assignment)
    (destination : s.getReg .x18 = BitVec.ofNat 64 (slotAddress n))
    (stored : OtherStorage s x n)
    (zero : MemBits s (BitVec.ofNat 64 (slotAddress n)) (0 : BitVec (graph.len n.fin)))
    (value : BitVec (graph.len n.fin)) (supported : value ∈ support (evalName x n)) :
    MemBits (nodeResult s n value) (BitVec.ofNat 64 (slotAddress n)) value := by
  cases n with
  | src k =>
    simp only [evalName, mem_support_pure_iff] at supported
    subst value
    exact zero
  | ci k t =>
    simp only [evalName, mem_support_pure_iff] at supported
    subst value
    dsimp only [nodeResult]
    apply (memBits_cast _ _ _ _).mpr
    exact (operation_tagged1_packing s (.ci k t) (prev k t) x _
      (nodeTag_literal _) destination stored (by simp [prev]; split <;> simp)).2.2
  | cv k t =>
    simp only [evalName, mem_support_pure_iff] at supported
    subst value
    dsimp only [nodeResult]
    apply (memBits_cast _ _ _ _).mpr
    exact (operation_copy_packing s (.cv k t) (.ch k t) x destination stored (by simp)).2.2
  | gc j =>
    simp only [evalName, mem_support_pure_iff] at supported
    subst value
    dsimp only [nodeResult]
    apply (memBits_cast _ _ _ _).mpr
    exact (operation_tagged3_packing s (.gc j) _ _ _ x _ (nodeTag_literal _)
      destination stored (by simp) (by simp) (by simp)).2.2
  | gv j =>
    simp only [evalName, mem_support_pure_iff] at supported
    subst value
    dsimp only [nodeResult]
    apply (memBits_cast _ _ _ _).mpr
    exact (operation_copy_packing s (.gv j) (.gh j) x destination stored (by simp)).2.2
  | ec l =>
    simp only [evalName, mem_support_pure_iff] at supported
    subst value
    dsimp only [nodeResult]
    apply (memBits_cast _ _ _ _).mpr
    exact (operation_tagged3_packing s (.ec l) _ _ _ x _ (nodeTag_literal _)
      destination stored (by simp) (by simp) (by simp)).2.2
  | ev l =>
    simp only [evalName, mem_support_pure_iff] at supported
    subst value
    dsimp only [nodeResult]
    apply (memBits_cast _ _ _ _).mpr
    exact (operation_copy_packing s (.ev l) (.eh l) x destination stored (by simp)).2.2
  | rc =>
    simp only [evalName, mem_support_pure_iff] at supported
    subst value
    dsimp only [nodeResult]
    apply (memBits_cast _ _ _ _).mpr
    exact (operation_tagged7_packing s .rc ev x _ (nodeTag_literal _)
      destination stored (by intro l; simp)).2.2
  | ch k t => exact hashResult_value s (.ch k t) (.ci k t) value (graph_len_fin _) destination
  | gh j => exact hashResult_value s (.gh j) (.gc j) value (graph_len_fin _) destination
  | eh l => exact hashResult_value s (.eh l) (.ec l) value (graph_len_fin _) destination
  | rh => exact hashResult_value s .rh .rc value (graph_len_fin _) destination

/-- An isolated ordinary block writes only its destination slot and retains its pointer. -/
def Isolated (dest : Name) (code : Code) : Prop :=
  ∀ s, s.getReg .x18 = BitVec.ofNat 64 (slotAddress dest) →
    SlotFrame s (code.foldl execInstrBr s) dest ∧
      (code.foldl execInstrBr s).getReg .x18 = BitVec.ofNat 64 (slotAddress dest)

theorem Isolated.nil (dest : Name) : Isolated dest [] :=
  fun s h => ⟨SlotFrame.refl s dest, h⟩

theorem Isolated.append {dest : Name} {a b : Code} (ha : Isolated dest a) (hb : Isolated dest b) :
    Isolated dest (a ++ b) := by
  intro s hs
  rw [List.foldl_append]
  obtain ⟨fa, ra⟩ := ha s hs
  obtain ⟨fb, rb⟩ := hb _ ra
  exact ⟨fa.trans fb, rb⟩

theorem Isolated.flatMap {α : Type} (dest : Name) (xs : List α) (f : α → Code)
    (each : ∀ x ∈ xs, Isolated dest (f x)) : Isolated dest (xs.flatMap f) := by
  induction xs with
  | nil => exact Isolated.nil dest
  | cons x xs ih =>
    exact (each x (by simp)).append (ih (by intro y hy; exact each y (by simp [hy])))

theorem copyChild_isolated (dest child : Name) (j : ℕ) (bounded : j + 1 < 16) :
    Isolated dest (copyChild child (8 * j)) := by
  intro s hs
  refine ⟨copyChild_slotFrame s dest child j bounded hs, ?_⟩
  rw [copyChild_register _ _ _ .x18 (by decide) (by decide) (by decide)]
  exact hs

theorem writeTag_isolated (dest : Name) (tag : BitVec 16) (j : ℕ) (bounded : j < 16)
    (literal : (literalValue tag.toNat).truncate 16 = tag) :
    Isolated dest (writeTag tag (8 * j)) := by
  intro s hs
  refine ⟨writeTag_slotFrame s dest tag j bounded literal hs, ?_⟩
  rw [writeTag_register _ _ _ .x18 (by decide)]
  exact hs

/-- Every deterministic operation confines its writes to the destination slot. -/
theorem operation_isolated (dest : Name) (op : NodeOp)
    (literal : match op with
      | .tagged1 tag _ | .tagged3 tag _ _ _ | .tagged7 tag _ =>
          (literalValue tag.toNat).truncate 16 = tag
      | _ => True) :
    match op with
    | .hash _ => True
    | _ => Isolated dest (operation op) := by
  cases op with
  | zero => exact Isolated.nil dest
  | copy child => exact copyChild_isolated dest child 0 (by decide)
  | tagged1 tag child =>
    exact (copyChild_isolated dest child 0 (by decide)).append
      (writeTag_isolated dest tag 2 (by decide) literal)
  | tagged3 tag a b c =>
    exact (((copyChild_isolated dest c 0 (by decide)).append
      (copyChild_isolated dest b 2 (by decide))).append
      (copyChild_isolated dest a 4 (by decide))).append
      (writeTag_isolated dest tag 6 (by decide) literal)
  | tagged7 tag children =>
    apply Isolated.append
    · apply Isolated.flatMap
      intro l hl
      have h : 16 * (6 - l.val) = 8 * (2 * (6 - l.val)) := by omega
      rw [h]
      exact copyChild_isolated dest _ _ (by omega)
    · exact writeTag_isolated dest tag 14 (by decide) literal
  | hash source => trivial

/-- HASH changes only the current node's slot. -/
theorem hashResult_slotFrame (s : MachineState) (dest source : Name) (value : BitVec 256)
    (destination : s.getReg .x18 = BitVec.ofNat 64 (slotAddress dest)) :
    SlotFrame s (Riscv.writeHash ((hashSetup source).foldl execInstrBr s) value) dest := by
  intro addr different
  rw [writeHash_frame]
  · exact congrFun (hashSetup_memory s source) addr
  · intro j hj
    rw [(hashSetup_registers s source).2.2, destination]
    exact different j (by omega)

/-- The operation result leaves all memory outside the current node untouched. -/
theorem nodeResult_frame (s : MachineState) (n : Name) (value : BitVec (graph.len n.fin))
    (destination : s.getReg .x18 = BitVec.ofNat 64 (slotAddress n)) :
    SlotFrame s (nodeResult s n value) n := by
  cases n with
  | ch k t => exact hashResult_slotFrame s (.ch k t) (.ci k t) _ destination
  | gh j => exact hashResult_slotFrame s (.gh j) (.gc j) _ destination
  | eh l => exact hashResult_slotFrame s (.eh l) (.ec l) _ destination
  | rh => exact hashResult_slotFrame s .rh .rc _ destination
  | src k => exact SlotFrame.refl s (.src k)
  | ci k t => exact (operation_isolated (.ci k t) (nodeOp (.ci k t)) (nodeTag_literal _) s destination).1
  | cv k t => exact (operation_isolated (.cv k t) (nodeOp (.cv k t)) trivial s destination).1
  | gc j => exact (operation_isolated (.gc j) (nodeOp (.gc j)) (nodeTag_literal _) s destination).1
  | gv j => exact (operation_isolated (.gv j) (nodeOp (.gv j)) trivial s destination).1
  | ec l => exact (operation_isolated (.ec l) (nodeOp (.ec l)) (nodeTag_literal _) s destination).1
  | ev l => exact (operation_isolated (.ev l) (nodeOp (.ev l)) trivial s destination).1
  | rc => exact (operation_isolated .rc (nodeOp .rc) (nodeTag_literal _) s destination).1

/-- Updating a slot and preserving all other slots realizes an assignment update. -/
theorem nodeStorage_update (s : MachineState) (x : graph.Assignment) (n : Name)
    (value : BitVec (graph.len n.fin)) (stored : OtherStorage s x n)
    (current : MemBits s (BitVec.ofNat 64 (slotAddress n)) value) :
    NodeStorage s (Function.update x n.fin value) := by
  intro other
  by_cases same : other = n
  · subst other
    simpa only [Function.update_self] using current
  · rw [Function.update_of_ne (fun equal => same (Name.fin_injective equal))]
    exact stored other same

/-- Exact operation values and slot isolation give the high-level assignment transition. -/
theorem nodeResult_storage (s : MachineState) (n : Name) (x : graph.Assignment)
    (destination : s.getReg .x18 = BitVec.ofNat 64 (slotAddress n))
    (stored : OtherStorage s x n)
    (zero : MemBits s (BitVec.ofNat 64 (slotAddress n)) (0 : BitVec (graph.len n.fin)))
    (value : BitVec (graph.len n.fin)) (supported : value ∈ support (evalName x n)) :
    NodeStorage (nodeResult s n value) (Function.update x n.fin value) :=
  nodeStorage_update _ x n value (stored.frame (nodeResult_frame s n value destination))
    (nodeResult_value s n x destination stored zero value supported)

/-- A block preserves a register for every starting machine state. -/
def PreservesRegister (r : Reg) (code : Code) : Prop :=
  ∀ s, (code.foldl execInstrBr s).getReg r = s.getReg r

theorem PreservesRegister.append {r : Reg} {a b : Code}
    (ha : PreservesRegister r a) (hb : PreservesRegister r b) : PreservesRegister r (a ++ b) := by
  intro s
  rw [List.foldl_append, hb, ha]

theorem PreservesRegister.flatMap {α : Type} (r : Reg) (xs : List α) (f : α → Code)
    (each : ∀ x ∈ xs, PreservesRegister r (f x)) : PreservesRegister r (xs.flatMap f) := by
  induction xs with
  | nil => intro s; rfl
  | cons x xs ih =>
    exact (each x (by simp)).append (ih (by intro y hy; exact each y (by simp [hy])))

/-- All deterministic node operations preserve the position and disclosure pointers. -/
theorem operation_preserves (op : NodeOp) (r : Reg) (h7 : r ≠ .x7) (h26 : r ≠ .x26)
    (h27 : r ≠ .x27) :
    match op with
    | .hash _ => True
    | _ => PreservesRegister r (operation op) := by
  cases op with
  | zero => intro s; rfl
  | copy child => exact fun s => copyChild_register s child 0 r h7 h26 h27
  | tagged1 tag child =>
    exact PreservesRegister.append (fun s => copyChild_register s child 0 r h7 h26 h27)
      (fun s => writeTag_register s tag 16 r h26)
  | tagged3 tag a b c =>
    exact PreservesRegister.append
      (PreservesRegister.append
        (PreservesRegister.append (fun s => copyChild_register s c 0 r h7 h26 h27)
          (fun s => copyChild_register s b 16 r h7 h26 h27))
        (fun s => copyChild_register s a 32 r h7 h26 h27))
      (fun s => writeTag_register s tag 48 r h26)
  | tagged7 tag children =>
    apply PreservesRegister.append
    · exact PreservesRegister.flatMap r _ _
        (fun l _ s => copyChild_register s (children l) _ r h7 h26 h27)
    · exact fun s => writeTag_register s tag 112 r h26
  | hash source => trivial

/-- Hash setup and output stores preserve the two persistent verifier pointers. -/
theorem hashResult_register (s : MachineState) (source : Name) (value : BitVec 256)
    (r : Reg) (h10 : r ≠ .x10) (h11 : r ≠ .x11) (h12 : r ≠ .x12) (h5 : r ≠ .x5) :
    (Riscv.writeHash ((hashSetup source).foldl execInstrBr s) value).getReg r = s.getReg r := by
  simp only [Riscv.writeHash, MachineState.getReg_setPC, MachineState.writeWords,
    getReg_store, hashSetup, List.foldl_append, List.foldl_cons, List.foldl_nil,
    execInstrBr, MachineState.getReg_setPC,
    MachineState.getReg_setReg_ne _ .x5 r _ h5.symm,
    MachineState.getReg_setReg_ne _ .x12 r _ h12.symm,
    constant_preserves _ .x11 r _ h11.symm, constant_preserves _ .x10 r _ h10.symm]

/-- Node operations preserve both the decoded-position and disclosure cursors. -/
theorem nodeResult_register (s : MachineState) (n : Name) (value : BitVec (graph.len n.fin))
    (r : Reg) (persistent : r = .x8 ∨ r = .x9) :
    (nodeResult s n value).getReg r = s.getReg r := by
  have h7 : r ≠ .x7 := by rcases persistent with rfl | rfl <;> decide
  have h26 : r ≠ .x26 := by rcases persistent with rfl | rfl <;> decide
  have h27 : r ≠ .x27 := by rcases persistent with rfl | rfl <;> decide
  have h10 : r ≠ .x10 := by rcases persistent with rfl | rfl <;> decide
  have h11 : r ≠ .x11 := by rcases persistent with rfl | rfl <;> decide
  have h12 : r ≠ .x12 := by rcases persistent with rfl | rfl <;> decide
  have h5 : r ≠ .x5 := by rcases persistent with rfl | rfl <;> decide
  cases n with
  | ch k t => exact hashResult_register s (.ci k t) _ r h10 h11 h12 h5
  | gh j => exact hashResult_register s (.gc j) _ r h10 h11 h12 h5
  | eh l => exact hashResult_register s (.ec l) _ r h10 h11 h12 h5
  | rh => exact hashResult_register s .rc _ r h10 h11 h12 h5
  | src k => exact operation_preserves (nodeOp (.src k)) r h7 h26 h27 s
  | ci k t => exact operation_preserves (nodeOp (.ci k t)) r h7 h26 h27 s
  | cv k t => exact operation_preserves (nodeOp (.cv k t)) r h7 h26 h27 s
  | gc j => exact operation_preserves (nodeOp (.gc j)) r h7 h26 h27 s
  | gv j => exact operation_preserves (nodeOp (.gv j)) r h7 h26 h27 s
  | ec l => exact operation_preserves (nodeOp (.ec l)) r h7 h26 h27 s
  | ev l => exact operation_preserves (nodeOp (.ev l)) r h7 h26 h27 s
  | rc => exact operation_preserves (nodeOp .rc) r h7 h26 h27 s

end OptimalOTS.RiscvUpperProgram.Direct
