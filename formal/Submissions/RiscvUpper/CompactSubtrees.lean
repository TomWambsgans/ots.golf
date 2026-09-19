import Submissions.RiscvUpper.CompactTree

/-! The subtree phase of the compact image: the seven subtree digests. -/

namespace OptimalOTS.RiscvUpperProgram.Compact

open RiscvZkvm.Rv64 Forest Forest.Name RiscvUpperForest.ForestVerifier OracleComp

set_option allowUnsafeReducibility true
attribute [local reducible] Forest.graph
attribute [local irreducible] Forest.fixedPositions Forest.fixedDigits

variable (index : Idx paperParams) (payload : List Bool) (pk : PublicKey paperParams)

/-! ## Subtree nodes -/

theorem evaluated_ec (l : Fin 7) : evaluated (fixedPositions index) (ec l) = decide (l.val < 5) := rfl
theorem evaluated_eh (l : Fin 7) : evaluated (fixedPositions index) (eh l) = decide (l.val < 5) := rfl
theorem evaluated_ev (l : Fin 7) : evaluated (fixedPositions index) (ev l) = decide (l.val < 5) := rfl
theorem disclosed_ev (l : Fin 7) : disclosed (fixedPositions index) (ev l) = decide (5 ≤ l.val) := rfl

theorem detVal_ev (l : Fin 7) (x : graph.Assignment) : detVal (.ev l) x = Forest.trunc (x (eh l).fin) := rfl

/-- The tagged subtree input of a processed node, in machine order. -/
def TaggedE (x : graph.Assignment) (l : Fin 7) : Prop :=
  x (ec l).fin = (tw (eh l) ++ cat3 (Forest.trunc (x (gv (groupOf l 0)).fin))
    (Forest.trunc (x (gv (groupOf l 1)).fin))
    (Forest.trunc (x (gv (groupOf l 2)).fin))).cast (graph_len_fin (ec l)).symm

theorem cursorStep_ec (l : Fin 7) (x : graph.Assignment) (cursor : ℕ) :
    cursorStep index payload x cursor (ec l) =
      if l.val < 5 then
        pure (Function.update x (ec l).fin
          ((tw (eh l) ++ cat3 (Forest.trunc (x (gv (groupOf l 0)).fin))
            (Forest.trunc (x (gv (groupOf l 1)).fin))
            (Forest.trunc (x (gv (groupOf l 2)).fin))).cast (graph_len_fin (ec l)).symm), cursor)
      else pure (Function.update x (ec l).fin 0, cursor) := by
  unfold cursorStep
  simp only [disclosed, Bool.false_eq_true, if_false, evaluated_ec, decide_eq_true_eq]
  split_ifs
  · rw [runOp_eq]
    simp only [evalName, map_pure, detVal_ec]
  · rfl

theorem cursorStep_eh (l : Fin 7) (x : graph.Assignment) (cursor : ℕ) :
    cursorStep index payload x cursor (eh l) =
      if l.val < 5 then
        (fun y => (Function.update x (eh l).fin (y.cast (graph_len_fin (eh l)).symm), cursor)) <$>
          hash paperParams (x (ec l).fin)
      else pure (Function.update x (eh l).fin 0, cursor) := by
  unfold cursorStep
  simp only [disclosed, Bool.false_eq_true, if_false, evaluated_eh, decide_eq_true_eq]
  split_ifs
  · rw [runOp_eq]
    simp only [evalName, Functor.map_map]
  · rfl

theorem cursorStep_ev (l : Fin 7) (x : graph.Assignment) (cursor : ℕ) :
    cursorStep index payload x cursor (ev l) =
      if 5 ≤ l.val then
        pure (Function.update x (ev l).fin
          (ofBits (graph.len (ev l).fin) ((payload.drop cursor).take (graph.len (ev l).fin))),
          cursor + 128)
      else
        pure (Function.update x (ev l).fin
          ((Forest.trunc (x (eh l).fin)).cast (graph_len_fin (ev l)).symm), cursor) := by
  unfold cursorStep
  simp only [disclosed_ev, evaluated_ev, decide_eq_true_eq]
  split_ifs with h h'
  · rfl
  · rw [runOp_eq]
    simp only [evalName, map_pure, detVal_ev]
  · omega

theorem consumedBits_ev (l : Fin 7) : consumedBits index (ev l) = if 5 ≤ l.val then 128 else 0 := by
  rw [consumedBits_word, disclosed_ev]
  by_cases h : 5 ≤ l.val <;> simp [h]

theorem ec_len (l : Fin 7) : graph.len (ec l).fin = 400 := graph_len_fin (ec l)
theorem eh_len_le (l : Fin 7) : graph.len (eh l).fin ≤ 256 := by
  rw [graph_len_fin]; norm_num [Name.len]
theorem ev_len_le (l : Fin 7) : graph.len (ev l).fin ≤ 256 := by
  rw [graph_len_fin]; norm_num [Name.len]

theorem subtreeTag_literal (l : Fin 7) :
    (literalValue (BitVec.ofNat 16 (2779 + l.val)).toNat).truncate 16 = BitVec.ofNat 16 (2779 + l.val) :=
  nodeTag_literal (.eh l)

/-! ## Frames around subtree slots -/

theorem subtreeAddr_toNat (l : ℕ) (hl : l < 7) : (subtreeAddr l).toNat = subtreesBase + subtreeSlot l := by
  simp only [subtreeAddr, subtreesBase, subtreeSlot, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem subtreeAddr_word_ne (l l' : ℕ) (hl : l < 7) (hl' : l' < 7) (i i' : ℕ) (hi : i < 4)
    (hi' : i' < 4) (different : l ≠ l') :
    subtreeAddr l + BitVec.ofNat 64 (8 * i) ≠ subtreeAddr l' + BitVec.ofNat 64 (8 * i') := by
  intro h
  have h' := congrArg BitVec.toNat h
  simp only [subtreeAddr, subtreesBase, subtreeSlot, BitVec.toNat_add, BitVec.toNat_ofNat] at h'
  omega

theorem subtree_ne_low (addr : Word) (low : addr.toNat < subtreesBase) (l : ℕ) (i : ℕ) (hl : l < 7)
    (hi : i < 4) : addr ≠ subtreeAddr l + BitVec.ofNat 64 (8 * i) := by
  intro h
  have h' := congrArg BitVec.toNat h
  simp only [subtreeAddr, subtreesBase, subtreeSlot, BitVec.toNat_add, BitVec.toNat_ofNat] at h'
  unfold subtreesBase at low
  omega

theorem subtreeAddr_low (l : ℕ) (hl : l < 7) (i : ℕ) (hi : i < 4) :
    (subtreeAddr l + BitVec.ofNat 64 (8 * i)).toNat < scratchBase := by
  simp only [subtreeAddr, subtreesBase, subtreeSlot, scratchBase, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem subtreeAddr_access (l : ℕ) (hl : l < 7) (i : ℕ) (hi : i < 4) :
    isValidDwordAccess (subtreeAddr l + BitVec.ofNat 64 (8 * i)) = true := by
  rw [subtreeAddr_word]
  exact subtree_access l i hl hi

/-- Writes into one subtree slot leave the other subtree slots alone. -/
theorem HoldsE.frame {s t : MachineState} {l l' : Fin 7} (different : l' ≠ l) {w : ℕ} (v : BitVec w)
    (small : w ≤ 256)
    (frame : ∀ addr, (∀ i, i < 4 → addr ≠ subtreeAddr l + BitVec.ofNat 64 (8 * i)) →
      addr.toNat < scratchBase → t.getMem addr = s.getMem addr)
    (held : HoldsE s l' v) : HoldsE t l' v := by
  apply memBits_of_word_frame s t _ v held
  intro i hi
  rw [aligned_bit_word _ ((aligned_iff _).mp (subtreeAddr_aligned l' l'.isLt)) i
    (by rw [subtreeAddr_toNat l' l'.isLt]; unfold subtreesBase subtreeSlot; omega)]
  apply frame
  · intro i' hi'
    exact subtreeAddr_word_ne l' l l'.isLt l.isLt (i / 64) i' (by omega) hi' (fun h => different (Fin.ext h))
  · exact subtreeAddr_low l' l'.isLt (i / 64) (by omega)

/-- Subtree slots survive writes into the scratch buffer and above. -/
theorem HoldsE.frameScratch {s t : MachineState} {l : Fin 7} {w : ℕ} (v : BitVec w)
    (small : w ≤ 256)
    (frame : ∀ addr : Word, addr.toNat < scratchBase → t.getMem addr = s.getMem addr)
    (held : HoldsE s l v) : HoldsE t l v := by
  apply memBits_frame_low _ frame held
  rw [subtreeAddr_toNat l l.isLt]
  unfold subtreesBase subtreeSlot scratchBase
  omega

/-- Group slots survive writes into the subtree array and above. -/
theorem holdsG_of_frame_subtrees {s t : MachineState} {j : Fin 21} (hj : j.val < 15) {w : ℕ}
    (v : BitVec w) (small : w ≤ 256)
    (frame : ∀ addr : Word, addr.toNat < subtreesBase → t.getMem addr = s.getMem addr)
    (held : HoldsG s j v) : HoldsG t j v := by
  apply memBits_of_word_frame s t _ v held
  intro i hi
  apply frame
  rw [aligned_bit_word _ ((aligned_iff _).mp (groupAddr_aligned j hj)) i
    (by rw [groupAddr_toNat j hj]; unfold groupsBase groupSlot; omega)]
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, groupAddr_toNat j hj]
  unfold groupsBase groupSlot subtreesBase
  omega

theorem frameInputs_of_frame_subtrees {s t : MachineState}
    (frame : ∀ addr : Word, addr.toNat < subtreesBase → t.getMem addr = s.getMem addr) :
    FrameInputs s t := by
  intro addr below
  apply frame
  unfold chainsBase at below
  unfold subtreesBase
  omega

/-- Group values, as the subtree phase reads them. -/
def GroupsHeld (s : MachineState) (x : graph.Assignment) : Prop :=
  ∀ j : Fin 21, j.val < 15 → HoldsG s j (x (gv j).fin)

theorem groupOf_lt (l : Fin 7) (hl : l.val < 5) (a : Fin 3) : (groupOf l a).val < 15 := by
  show 3 * l.val + a.val < 15
  have := a.isLt
  omega

/-! ## Subtree inputs -/

def EcInv (after : List Name) (s : MachineState) (x : graph.Assignment) (cursor : ℕ)
    (rem : List Name) : Prop :=
  TreeCtx index payload pk s cursor (rem ++ after) ∧ GroupsHeld s x ∧
  ∀ l : Fin 7, l.val < 5 → ec l ∉ rem → TaggedE x l

def ecSeg (after : List Name) : Segment := ⟨fun _ => [], fun _ => 0, EcInv index payload pk after⟩

theorem ec_refines (after : List Name) (l : Fin 7) :
    (ecSeg index payload pk after).NodeRefines index payload (ec l) := by
  apply Segment.NodeRefines.ofPure
  · rfl
  · rfl
  · intro s x cursor rest _ inv r hr
    obtain ⟨ctx, held, tagged⟩ := inv
    rw [cursorStep_ec] at hr
    have value : ∃ v, r = (Function.update x (ec l).fin v, cursor) ∧
        (l.val < 5 → v = (tw (eh l) ++ cat3 (Forest.trunc (x (gv (groupOf l 0)).fin))
          (Forest.trunc (x (gv (groupOf l 1)).fin))
          (Forest.trunc (x (gv (groupOf l 2)).fin))).cast (graph_len_fin (ec l)).symm) := by
      split_ifs at hr with h
      · simp only [support_pure, Set.mem_singleton_iff] at hr
        exact ⟨_, hr, fun _ => rfl⟩
      · simp only [support_pure, Set.mem_singleton_iff] at hr
        exact ⟨_, hr, fun hl => absurd hl h⟩
    obtain ⟨v, rfl, hv⟩ := value
    refine ⟨ctx.drop, ?_, ?_⟩
    · intro j hj
      show HoldsG s j (Function.update x (ec l).fin v (gv j).fin)
      rw [Function.update_of_ne (fin_ne_of_ne (by simp : gv j ≠ ec l))]
      exact held j hj
    · intro l' hl' notin
      unfold TaggedE
      dsimp only
      rw [Function.update_of_ne (fin_ne_of_ne (by simp : gv (groupOf l' 0) ≠ ec l)),
        Function.update_of_ne (fin_ne_of_ne (by simp : gv (groupOf l' 1) ≠ ec l)),
        Function.update_of_ne (fin_ne_of_ne (by simp : gv (groupOf l' 2) ≠ ec l))]
      by_cases same : l' = l
      · subst same
        rw [Function.update_self, hv hl']
      · rw [Function.update_of_ne (fin_ne_of_ne (fun h => same (Name.ec.inj h)))]
        exact tagged l' hl' (by simp only [List.mem_cons, not_or]; exact ⟨fun h => same (Name.ec.inj h), notin⟩)
  · intro x cursor
    by_cases h : l.val < 5
    · exact ⟨_, by rw [cursorStep_ec, if_pos h]⟩
    · exact ⟨_, by rw [cursorStep_ec, if_neg h]⟩

/-! ## Subtree hashes -/

def subtreeLin (l : ℕ) : Code :=
  tripleInput .x20 (groupSlot (3 * l)) (groupSlot (3 * l + 1)) (groupSlot (3 * l + 2)) (2779 + l) ++
  [.ADDI .x10 .x18 0, .ADDI .x12 .x21 (BitVec.ofNat 12 (subtreeSlot l))]

theorem subtreeBlock_parts (l : ℕ) : subtreeBlock l = subtreeLin l ++ [Instr.ECALL] := by
  simp [subtreeBlock, subtreeLin, List.append_assoc]

theorem subtreeBlock_length (l : ℕ) : (subtreeBlock l).length = (subtreeLin l).length + 1 := by
  rw [subtreeBlock_parts]; simp

/-- The linear part of a subtree block loads the exact 400-bit subtree input into scratch and
points the hash at it and at the subtree's slot. -/
theorem subtreeLin_effect (s : MachineState) (l : Fin 7) (hl : l.val < 5) (regs : TreeRegs s)
    (x : graph.Assignment) (held : GroupsHeld s x) (tagged : TaggedE x l) :
    Riscv.LinearReady s (subtreeLin l) ∧
    ((subtreeLin l).foldl execInstrBr s).getReg .x10 = scratchAddr ∧
    ((subtreeLin l).foldl execInstrBr s).getReg .x12 = subtreeAddr l ∧
    (∀ r, r ≠ .x10 → r ≠ .x12 → r ≠ .x26 → r ≠ .x27 →
      ((subtreeLin l).foldl execInstrBr s).getReg r = s.getReg r) ∧
    (∀ addr : Word, addr.toNat < scratchBase →
      ((subtreeLin l).foldl execInstrBr s).getMem addr = s.getMem addr) ∧
    MemBits ((subtreeLin l).foldl execInstrBr s) scratchAddr (x (ec l).fin) := by
  have h0 : (groupOf l 0).val < 15 := groupOf_lt l hl 0
  have h1 : (groupOf l 1).val < 15 := groupOf_lt l hl 1
  have h2 : (groupOf l 2).val < 15 := groupOf_lt l hl 2
  have slot : ∀ j, j < 15 → groupSlot j + 8 < 2048 := by intro j hj; unfold groupSlot; omega
  have source : ∀ j : Fin 21, j.val < 15 →
      MemBits s (s.getReg .x20 + BitVec.ofNat 64 (groupSlot j)) (Forest.trunc (x (gv j).fin)) := by
    intro j hj
    rw [regs.groups]
    exact memBits_trunc (held j hj)
  have access : ∀ off, off = groupSlot (groupOf l 0) ∨ off = groupSlot (groupOf l 0) + 8 ∨
      off = groupSlot (groupOf l 1) ∨ off = groupSlot (groupOf l 1) + 8 ∨
      off = groupSlot (groupOf l 2) ∨ off = groupSlot (groupOf l 2) + 8 →
      isValidDwordAccess (s.getReg .x20 + BitVec.ofNat 64 off) = true := by
    intro off hoff
    rw [regs.groups]
    rcases hoff with h | h | h | h | h | h <;> subst h
    · simpa only [Nat.mul_zero, Nat.add_zero] using group_access _ 0 h0 (by decide)
    · simpa only [Nat.mul_one] using group_access _ 1 h0 (by decide)
    · simpa only [Nat.mul_zero, Nat.add_zero] using group_access _ 0 h1 (by decide)
    · simpa only [Nat.mul_one] using group_access _ 1 h1 (by decide)
    · simpa only [Nat.mul_zero, Nat.add_zero] using group_access _ 0 h2 (by decide)
    · simpa only [Nat.mul_one] using group_access _ 1 h2 (by decide)
  have aligned : ∀ off, off = groupSlot (groupOf l 0) ∨ off = groupSlot (groupOf l 1) ∨
      off = groupSlot (groupOf l 2) →
      alignToDword (s.getReg .x20 + BitVec.ofNat 64 off) = s.getReg .x20 + BitVec.ofNat 64 off := by
    intro off hoff
    rw [regs.groups]
    rcases hoff with h | h | h <;> subst h
    · exact groupAddr_aligned _ h0
    · exact groupAddr_aligned _ h1
    · exact groupAddr_aligned _ h2
  have low : (s.getReg .x20).toNat + 4096 ≤ scratchBase := by rw [regs.groups]; decide
  obtain ⟨ready, tregs, frame, packed⟩ := tripleInput_effect s .x20 (groupSlot (groupOf l 0))
    (groupSlot (groupOf l 1)) (groupSlot (groupOf l 2)) (2779 + l.val) _ _ _ (by decide) (by decide)
    (slot _ h0) (slot _ h1) (slot _ h2) (subtreeTag_literal l) regs.scratch low access aligned
    (source _ h0) (source _ h1) (source _ h2)
  have same : tripleInput .x20 (groupSlot (groupOf l 0)) (groupSlot (groupOf l 1))
      (groupSlot (groupOf l 2)) (2779 + l.val) =
      tripleInput .x20 (groupSlot (3 * l.val)) (groupSlot (3 * l.val + 1))
        (groupSlot (3 * l.val + 2)) (2779 + l.val) := rfl
  rw [same] at ready tregs frame packed
  generalize hu : (tripleInput .x20 (groupSlot (3 * l.val)) (groupSlot (3 * l.val + 1))
    (groupSlot (3 * l.val + 2)) (2779 + l.val)).foldl execInstrBr s = u at tregs frame packed
  have hsub : subtreeSlot l < 2048 := by unfold subtreeSlot; omega
  have zero : signExtend12 (0 : BitVec 12) = 0#64 := by decide
  have unfolded : (subtreeLin l).foldl execInstrBr s =
      [Instr.ADDI .x10 .x18 0, .ADDI .x12 .x21 (BitVec.ofNat 12 (subtreeSlot l))].foldl execInstrBr u := by
    simp only [subtreeLin, List.foldl_append, hu]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ready.append ⟨rfl, trivial, rfl, trivial, trivial⟩
  · rw [unfolded]
    simp only [List.foldl_cons, List.foldl_nil, execInstrBr, zero,
      MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ .x12 .x10 _ (by decide),
      MachineState.getReg_setReg_eq (by decide : Reg.x10 ≠ .x0)]
    rw [tregs .x18 (by decide) (by decide), regs.scratch, BitVec.add_zero]
  · rw [unfolded]
    simp only [List.foldl_cons, List.foldl_nil, execInstrBr,
      signExtend12_nonnegative (subtreeSlot l) hsub, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x12 ≠ .x0),
      MachineState.getReg_setReg_ne _ .x10 .x21 _ (by decide)]
    rw [tregs .x21 (by decide) (by decide), regs.subtrees]
    rfl
  · intro r h10 h12 h26 h27
    rw [unfolded]
    simp only [List.foldl_cons, List.foldl_nil, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ .x12 r _ h12.symm,
      MachineState.getReg_setReg_ne _ .x10 r _ h10.symm]
    exact tregs r h26 h27
  · intro addr low'
    rw [unfolded]
    simp only [List.foldl_cons, List.foldl_nil, execInstrBr, MachineState.getMem_setPC,
      MachineState.getMem_setReg]
    exact frame addr low'
  · rw [unfolded]
    simp only [List.foldl_cons, List.foldl_nil, execInstrBr]
    have value : MemBits u scratchAddr (x (ec l).fin) := by
      rw [tagged]
      apply (memBits_cast _ _ _ _).mpr
      rw [cat3_assoc]
      exact packed
    exact memBits_of_mem_eq rfl value

def ehCode : Name → Code
  | .eh l => if l.val < 5 then subtreeBlock l.val else []
  | _ => []

def ehCost : Name → ℕ
  | .eh l => if l.val < 5 then (subtreeBlock l.val).length else 0
  | _ => 0

def EhInv (after : List Name) (s : MachineState) (x : graph.Assignment) (cursor : ℕ)
    (rem : List Name) : Prop :=
  TreeCtx index payload pk s cursor (rem ++ after) ∧ GroupsHeld s x ∧
  ∀ l : Fin 7, l.val < 5 → (eh l ∈ rem → TaggedE x l) ∧ (eh l ∉ rem → HoldsE s l (x (eh l).fin))

def ehSeg (after : List Name) : Segment := ⟨ehCode, ehCost, EhInv index payload pk after⟩

theorem eh_refines (after : List Name) (l : Fin 7) :
    (ehSeg index payload pk after).NodeRefines index payload (eh l) := by
  by_cases hl : l.val < 5
  · intro s x cursor rest tail K c budget fuel fresh inv located0 bound continuation
    obtain ⟨ctx, held, facts⟩ := inv
    have code : ehCode (eh l) = subtreeBlock l := by simp [ehCode, hl]
    have cost : ehCost (eh l) = (subtreeBlock l).length := by simp [ehCost, hl]
    change Riscv.CodeAt s s.pc (ehCode (eh l) ++ tail) at located0
    change (ehCode (eh l)).length + budget ≤ fuel at bound
    rw [code] at located0 bound
    change Riscv.Refines fuel s _ (ehCost (eh l) + c)
    rw [cost, cursorStep_eh, if_pos hl]
    have located := located0
    rw [subtreeBlock_parts, List.append_assoc] at located
    rw [subtreeBlock_length] at bound
    obtain ⟨ready, w10, w12, wRegs, wFrame, wValue⟩ :=
      subtreeLin_effect s l hl ctx.regs x held ((facts l hl).1 (by simp))
    set w := (subtreeLin l).foldl execInstrBr s with hw
    have wPc : w.pc = s.pc + BitVec.ofNat 64 (4 * (subtreeLin l).length) :=
      Riscv.linear_fold_pc s _ ready
    have wCode : Riscv.CodeAt w w.pc ([Instr.ECALL] ++ tail) := by
      rw [wPc]; exact located.append_right.code_eq (Riscv.fold_code s _)
    have wCodeEq : w.code = s.code := Riscv.fold_code s _
    have wFetch : w.code w.pc = some .ECALL := wCode.head
    have wCall : w.getReg .x5 = Riscv.hashCall := by
      rw [wRegs .x5 (by decide) (by decide) (by decide) (by decide)]; exact ctx.regs.call
    have wLen : w.getReg .x11 = 400 := by
      rw [wRegs .x11 (by decide) (by decide) (by decide) (by decide)]; exact ctx.regs.length
    have wValid : Riscv.hashArgumentsValid w = true := by
      simp only [Riscv.hashArgumentsValid, w10, w12, wLen, Bool.and_eq_true]
      refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
      · show isValidOutputRange scratchAddr 50 = true
        exact scratch_output_range_50
      · have h := subtreeAddr_access l l.isLt 0 (by decide)
        rwa [Nat.mul_zero, BitVec.add_zero] at h
      · have h := subtreeAddr_access l l.isLt 1 (by decide)
        rwa [show BitVec.ofNat 64 (8 * 1) = (8 : Word) from rfl] at h
      · have h := subtreeAddr_access l l.isLt 2 (by decide)
        rwa [show BitVec.ofNat 64 (8 * 2) = (16 : Word) from rfl] at h
      · have h := subtreeAddr_access l l.isLt 3 (by decide)
        rwa [show BitVec.ofNat 64 (8 * 3) = (24 : Word) from rfl] at h
    have wInput : Riscv.hashInput w = ⟨graph.len (ec l).fin, x (ec l).fin⟩ :=
      hashInput_of_memBits w10 (by rw [wLen, ec_len]; rfl) wValue
    have blocks : blockCost paperParams (graph.len (ec l).fin) = 1 := by rw [ec_len]; decide
    rw [subtreeBlock_length, show (subtreeLin l).length + 1 + c = (subtreeLin l).length + (1 + c) by omega,
      show fuel = (subtreeLin l).length + ((fuel - (subtreeLin l).length - 1) + 1) by omega]
    apply Riscv.Refines.linear _ located.append_left ready
    rw [← hw]
    simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp_apply, pure_bind]
    have step := Riscv.Refines.hash (fuel := fuel - (subtreeLin l).length - 1) wFetch wCall wValid
      (k := fun y => K (Function.update x (eh l).fin (y.cast (graph_len_fin (eh l)).symm), cursor))
      (c := c) ?_
    · rw [wInput, blocks] at step
      exact step
    intro y
    set v := Riscv.writeHash w y with hv
    have vRegs : ∀ r, r ≠ .x10 → r ≠ .x12 → r ≠ .x26 → r ≠ .x27 → v.getReg r = s.getReg r := by
      intro r h10 h12 h26 h27
      rw [hv, writeHash_regs, wRegs r h10 h12 h26 h27]
    have slotFrame : ∀ addr, (∀ i, i < 4 → addr ≠ subtreeAddr l + BitVec.ofNat 64 (8 * i)) →
        addr.toNat < scratchBase → v.getMem addr = s.getMem addr := by
      intro addr outside low
      rw [hv, writeHash_frame _ _ _ (by rw [w12]; exact outside), wFrame addr low]
    have lowFrame : ∀ addr : Word, addr.toNat < subtreesBase → v.getMem addr = s.getMem addr := by
      intro addr low
      apply slotFrame addr (fun i hi => subtree_ne_low addr low l i l.isLt hi)
      unfold subtreesBase at low
      unfold scratchBase
      omega
    have vPc : v.pc = s.pc + BitVec.ofNat 64 (4 * (subtreeBlock l).length) := by
      rw [hv, writeHash_pc, wPc, subtreeBlock_length,
        show (4 : Word) = BitVec.ofNat 64 4 from rfl, pcAdd,
        show 4 * (subtreeLin l).length + 4 = 4 * ((subtreeLin l).length + 1) by omega]
    have vCode : v.code = s.code := by rw [hv, writeHash_code, wCodeEq]
    have vLocated : Riscv.CodeAt v v.pc tail := by
      rw [vPc]; exact located0.append_right.code_eq vCode
    have answer : HoldsE v l ((y.cast (graph_len_fin (eh l)).symm : BitVec (graph.len (eh l).fin))) := by
      unfold HoldsE
      apply (memBits_cast _ _ _ _).mpr
      have h := writeHash_memBits w y (by rw [w12]; exact subtreeAddr_aligned l l.isLt)
      rw [w12] at h
      exact h
    apply continuation v (Function.update x (eh l).fin (y.cast (graph_len_fin (eh l)).symm), cursor)
      ?_ ?_ vLocated (fuel - (subtreeLin l).length - 1) (by omega)
    · rw [cursorStep_eh, if_pos hl, support_map]
      exact ⟨y, mem_support_hash _ y, rfl⟩
    · refine ⟨ctx.step (frameInputs_of_frame_subtrees lowFrame) ?_, ?_, ?_⟩
      · intro r hr
        apply vRegs r <;> rintro rfl <;> simp at hr
      · intro j hj
        show HoldsG v j (Function.update x (eh l).fin _ (gv j).fin)
        rw [Function.update_of_ne (fin_ne_of_ne (by simp : gv j ≠ eh l))]
        exact holdsG_of_frame_subtrees hj _ (gv_len_le j) lowFrame (held j hj)
      · intro l' hl'
        dsimp only
        by_cases same : l' = l
        · subst same
          refine ⟨fun h => absurd h fresh, fun _ => ?_⟩
          rw [Function.update_self]
          exact answer
        · have neEh : (eh l').fin ≠ (eh l).fin := fin_ne_of_ne (fun h => same (Name.eh.inj h))
          refine ⟨fun hmem => ?_, fun hnot => ?_⟩
          · have t := (facts l' hl').1 (by simp [hmem])
            unfold TaggedE at t ⊢
            rw [Function.update_of_ne (fin_ne_of_ne (by simp : ec l' ≠ eh l)),
              Function.update_of_ne (fin_ne_of_ne (by simp : gv (groupOf l' 0) ≠ eh l)),
              Function.update_of_ne (fin_ne_of_ne (by simp : gv (groupOf l' 1) ≠ eh l)),
              Function.update_of_ne (fin_ne_of_ne (by simp : gv (groupOf l' 2) ≠ eh l))]
            exact t
          · have hnot' : eh l' ∉ eh l :: rest := by
              simp only [List.mem_cons, not_or]
              exact ⟨fun h => same (Name.eh.inj h), hnot⟩
            rw [Function.update_of_ne neEh]
            exact HoldsE.frame same _ (eh_len_le l') slotFrame ((facts l' hl').2 hnot')
  · apply Segment.NodeRefines.ofPure
    · simp [ehSeg, ehCode, hl]
    · simp [ehSeg, ehCost, hl]
    · intro s x cursor rest _ inv r hr
      obtain ⟨ctx, held, facts⟩ := inv
      rw [cursorStep_eh, if_neg hl] at hr
      simp only [support_pure, Set.mem_singleton_iff] at hr
      subst hr
      refine ⟨ctx.drop, ?_, ?_⟩
      · intro j hj
        show HoldsG s j (Function.update x (eh l).fin 0 (gv j).fin)
        rw [Function.update_of_ne (fin_ne_of_ne (by simp : gv j ≠ eh l))]
        exact held j hj
      · intro l' hl'
        dsimp only
        have same : l' ≠ l := fun h => hl (h ▸ hl')
        have neEh : (eh l').fin ≠ (eh l).fin := fin_ne_of_ne (fun h => same (Name.eh.inj h))
        refine ⟨fun hmem => ?_, fun hnot => ?_⟩
        · have t := (facts l' hl').1 (by simp [hmem])
          unfold TaggedE at t ⊢
          rw [Function.update_of_ne (fin_ne_of_ne (by simp : ec l' ≠ eh l)),
            Function.update_of_ne (fin_ne_of_ne (by simp : gv (groupOf l' 0) ≠ eh l)),
            Function.update_of_ne (fin_ne_of_ne (by simp : gv (groupOf l' 1) ≠ eh l)),
            Function.update_of_ne (fin_ne_of_ne (by simp : gv (groupOf l' 2) ≠ eh l))]
          exact t
        · have hnot' : eh l' ∉ eh l :: rest := by
            simp only [List.mem_cons, not_or]
            exact ⟨fun h => same (Name.eh.inj h), hnot⟩
          rw [Function.update_of_ne neEh]
          exact (facts l' hl').2 hnot'
    · intro x cursor
      exact ⟨_, by rw [cursorStep_eh, if_neg hl]⟩

/-! ## Subtree values -/

def evCode : Name → Code
  | .ev l => if 5 ≤ l.val then readSubtree l.val else []
  | _ => []

def evCost : Name → ℕ
  | .ev l => if 5 ≤ l.val then (readSubtree l.val).length else 0
  | _ => 0

def EvInv (after : List Name) (s : MachineState) (x : graph.Assignment) (cursor : ℕ)
    (rem : List Name) : Prop :=
  TreeCtx index payload pk s cursor (rem ++ after) ∧
  ∀ l : Fin 7, (ev l ∈ rem → l.val < 5 → HoldsE s l (x (eh l).fin)) ∧ (ev l ∉ rem → HoldsE s l (x (ev l).fin))

def evSeg (after : List Name) : Segment := ⟨evCode, evCost, EvInv index payload pk after⟩

theorem readSubtree_effect (s : MachineState) (l : ℕ) :
    ((readSubtree l).foldl execInstrBr s).getReg .x9 = s.getReg .x9 + 16 ∧
    (∀ r, r ≠ .x9 → r ≠ .x26 → r ≠ .x27 →
      ((readSubtree l).foldl execInstrBr s).getReg r = s.getReg r) ∧
    ((readSubtree l).foldl execInstrBr s).mem =
      ((copy128 .x9 0 .x21 (subtreeSlot l)).foldl execInstrBr s).mem := by
  have h16 : signExtend12 (16 : BitVec 12) = (16 : Word) := by decide
  simp only [readSubtree, List.foldl_append, List.foldl_cons, List.foldl_nil, execInstrBr, h16]
  refine ⟨?_, ?_, rfl⟩
  · simp only [MachineState.getReg_setPC, MachineState.getReg_setReg_eq (by decide : Reg.x9 ≠ .x0),
      copy128_reg _ .x9 .x21 .x9 0 _ (by decide) (by decide)]
  · intro r h9 h26 h27
    simp only [MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ .x9 r _ h9.symm,
      copy128_reg _ .x9 .x21 r 0 _ h26 h27]

theorem readSubtree_ready (s : MachineState) (l : ℕ) (hl : l < 7)
    (base : s.getReg .x21 = BitVec.ofNat 64 subtreesBase) (cursor : CursorReady s) :
    Riscv.LinearReady s (readSubtree l) := by
  refine (copy128_ready s .x9 .x21 0 (subtreeSlot l) (by decide) (by decide) (by decide)
    ?_ ?_ ?_ ?_).append ?_
  · simpa only [signExtend12_nonnegative 0 (by decide)] using
      cursor_access s cursor 0 (by decide)
  · simpa only [signExtend12_nonnegative 8 (by decide)] using
      cursor_access s cursor 1 (by decide)
  · rw [signExtend12_nonnegative (subtreeSlot l) (by unfold subtreeSlot; omega), base]
    simpa only [Nat.mul_zero, Nat.add_zero] using subtree_access l 0 hl (by decide)
  · rw [signExtend12_nonnegative (subtreeSlot l + 8) (by unfold subtreeSlot; omega), base]
    simpa only [Nat.mul_one] using subtree_access l 1 hl (by decide)
  · exact ⟨rfl, trivial, trivial⟩

theorem ev_value (l : Fin 7) (cursor : ℕ) (t : MachineState)
    (held : MemBits t (subtreeAddr l) (ofBits 128 (payload.drop cursor))) :
    HoldsE t l (ofBits (graph.len (ev l).fin) ((payload.drop cursor).take (graph.len (ev l).fin))) := by
  have length : graph.len (ev l).fin = 128 := graph_len_fin (ev l)
  unfold HoldsE
  rw [length]
  have take : ofBits 128 ((payload.drop cursor).take 128) = ofBits 128 (payload.drop cursor) := by
    simpa only [List.drop_zero] using
      ofBits_drop_take (payload.drop cursor) (cap := 128) (start := 0) (len := 128) (by decide)
  rw [take]
  exact held

theorem ev_refines (after : List Name) (l : Fin 7) :
    (evSeg index payload pk after).NodeRefines index payload (ev l) := by
  by_cases hl : 5 ≤ l.val
  · intro s x cursor rest tail K c budget fuel fresh inv located0 bound continuation
    obtain ⟨ctx, facts⟩ := inv
    have code : evCode (ev l) = readSubtree l := by simp [evCode, hl]
    have cost : evCost (ev l) = (readSubtree l).length := by simp [evCost, hl]
    change Riscv.CodeAt s s.pc (evCode (ev l) ++ tail) at located0
    change (evCode (ev l)).length + budget ≤ fuel at bound
    rw [code] at located0 bound
    change Riscv.Refines fuel s _ (evCost (ev l) + c)
    rw [cost, cursorStep_ev, if_pos hl, pure_bind]
    have consumed : consumedBits index (ev l) = 128 := by rw [consumedBits_ev, if_pos hl]
    have room : cursor + 128 ≤ 5248 := ctx.room consumed
    have cursorReady : CursorReady s := ctx.atCursor.ready ctx.bounded ctx.aligned
    have ready := readSubtree_ready s l l.isLt ctx.regs.subtrees cursorReady
    obtain ⟨tCursor, tRegs, tMem⟩ := readSubtree_effect s l
    set t := (readSubtree l).foldl execInstrBr s with ht
    have tPc : t.pc = s.pc + BitVec.ofNat 64 (4 * (readSubtree l).length) :=
      Riscv.linear_fold_pc s _ ready
    have tLocated : Riscv.CodeAt t t.pc tail := by
      rw [tPc]; exact located0.append_right.code_eq (Riscv.fold_code s _)
    have hslot : subtreeSlot l + 8 < 2048 := by unfold subtreeSlot; omega
    have hslot' : subtreeSlot l < 2048 := by omega
    have source : MemBits s (s.getReg .x9 + BitVec.ofNat 64 0) (ofBits 128 (payload.drop cursor)) := by
      rw [BitVec.add_zero]
      exact ctx.context.payload_word cursor ctx.atCursor ctx.aligned room
    have moved := copy128_memBits s .x9 .x21 0 (subtreeSlot l) (by decide) (by decide) (by decide)
      (by decide) hslot (by rw [BitVec.add_zero]; exact (aligned_iff _).mpr cursorReady.2.2)
      (by rw [ctx.regs.subtrees]; exact subtreeAddr_aligned l l.isLt) (ofBits 128 (payload.drop cursor))
      source
    rw [ctx.regs.subtrees] at moved
    have value : HoldsE t l (ofBits (graph.len (ev l).fin)
        ((payload.drop cursor).take (graph.len (ev l).fin))) :=
      ev_value payload l cursor t (memBits_of_mem_eq tMem moved)
    have frame : ∀ addr, (∀ i, i < 4 → addr ≠ subtreeAddr l + BitVec.ofNat 64 (8 * i)) →
        t.getMem addr = s.getMem addr := by
      intro addr outside
      have h : t.getMem addr = ((copy128 .x9 0 .x21 (subtreeSlot l)).foldl execInstrBr s).getMem addr := by
        simp only [MachineState.getMem, tMem]
      rw [h, copy128_getMem _ _ _ _ _ (by decide) (by decide) (by decide)]
      simp only [signExtend12_nonnegative 0 (by decide), signExtend12_nonnegative (0 + 8) (by decide),
        signExtend12_nonnegative (subtreeSlot l) hslot', signExtend12_nonnegative (subtreeSlot l + 8) hslot,
        ctx.regs.subtrees]
      have o0 : addr ≠ BitVec.ofNat 64 subtreesBase + BitVec.ofNat 64 (subtreeSlot l) := by
        have := outside 0 (by decide)
        rwa [subtreeAddr_word, Nat.mul_zero, Nat.add_zero] at this
      have o1 : addr ≠ BitVec.ofNat 64 subtreesBase + BitVec.ofNat 64 (subtreeSlot l + 8) := by
        have := outside 1 (by decide)
        rwa [subtreeAddr_word, Nat.mul_one] at this
      rw [if_neg o1, if_neg o0]
    have lowFrame : FrameInputs s t := by
      intro addr low
      apply frame addr
      intro i hi
      exact subtree_ne_low addr (by unfold chainsBase at low; unfold subtreesBase; omega) l i l.isLt hi
    have frame' : ∀ addr, (∀ i, i < 4 → addr ≠ subtreeAddr l + BitVec.ofNat 64 (8 * i)) →
        addr.toNat < scratchBase → t.getMem addr = s.getMem addr :=
      fun addr outside _ => frame addr outside
    rw [show fuel = (readSubtree l).length + (fuel - (readSubtree l).length) by omega]
    apply Riscv.Refines.linear _ located0.append_left ready
    rw [← ht]
    apply continuation t (Function.update x (ev l).fin
      (ofBits (graph.len (ev l).fin) ((payload.drop cursor).take (graph.len (ev l).fin))), cursor + 128)
      (by rw [cursorStep_ev, if_pos hl]; simp) ?_ tLocated (fuel - (readSubtree l).length) (by omega)
    refine ⟨ctx.read consumed lowFrame ?_ tCursor, ?_⟩
    · intro r hr
      apply tRegs r <;> rintro rfl <;> simp at hr
    · intro l'
      dsimp only
      by_cases same : l' = l
      · subst same
        refine ⟨fun h => absurd h fresh, fun _ => ?_⟩
        rw [Function.update_self]
        exact value
      · have neEv : (ev l').fin ≠ (ev l).fin := fin_ne_of_ne (fun h => same (Name.ev.inj h))
        have neEh : (eh l').fin ≠ (ev l).fin := fin_ne_of_ne (by simp)
        refine ⟨fun hmem hl5 => ?_, fun hnot => ?_⟩
        · rw [Function.update_of_ne neEh]
          exact HoldsE.frame same _ (eh_len_le l') frame' ((facts l').1 (by simp [hmem]) hl5)
        · have hnot' : ev l' ∉ ev l :: rest := by
            simp only [List.mem_cons, not_or]
            exact ⟨fun h => same (Name.ev.inj h), hnot⟩
          rw [Function.update_of_ne neEv]
          exact HoldsE.frame same _ (ev_len_le l') frame' ((facts l').2 hnot')
  · apply Segment.NodeRefines.ofPure
    · simp [evSeg, evCode, hl]
    · simp [evSeg, evCost, hl]
    · intro s x cursor rest fresh inv r hr
      obtain ⟨ctx, facts⟩ := inv
      rw [cursorStep_ev, if_neg hl] at hr
      simp only [support_pure, Set.mem_singleton_iff] at hr
      subst hr
      refine ⟨ctx.drop, ?_⟩
      intro l'
      dsimp only
      by_cases same : l' = l
      · subst same
        refine ⟨fun hmem => absurd hmem fresh, fun _ => ?_⟩
        rw [Function.update_self]
        unfold HoldsE
        apply (memBits_cast _ _ _ _).mpr
        exact memBits_trunc ((facts l').1 (by simp) (by omega))
      · have neEv : (ev l').fin ≠ (ev l).fin := fin_ne_of_ne (fun h => same (Name.ev.inj h))
        have neEh : (eh l').fin ≠ (ev l).fin := fin_ne_of_ne (by simp)
        refine ⟨fun hmem hl5 => ?_, fun hnot => ?_⟩
        · rw [Function.update_of_ne neEh]
          exact (facts l').1 (by simp [hmem]) hl5
        · have hnot' : ev l' ∉ ev l :: rest := by
            simp only [List.mem_cons, not_or]
            exact ⟨fun h => same (Name.ev.inj h), hnot⟩
          rw [Function.update_of_ne neEv]
          exact (facts l').2 hnot'
    · intro x cursor
      exact ⟨_, by rw [cursorStep_ev, if_neg hl]⟩

/-! ## The subtree phase -/

theorem ecs_code (after : List Name) : ecs.flatMap (ecSeg index payload pk after).code = [] := by
  simp [ecs, ecSeg, List.flatMap_eq_nil_iff]

theorem ehs_code (after : List Name) :
    ehs.flatMap (ehSeg index payload pk after).code = subtreeHashes := by
  simp only [ehs, ehSeg, List.flatMap_map, subtreeHashes]
  rfl

theorem evs_code (after : List Name) :
    evs.flatMap (evSeg index payload pk after).code = subtreeReads := by
  simp only [evs, evSeg, List.flatMap_map, subtreeReads]
  rfl

theorem ecs_cost (after : List Name) : (ecs.map (ecSeg index payload pk after).cost).sum = 0 := by
  apply List.sum_eq_zero
  intro v hv
  obtain ⟨_, _, rfl⟩ := List.mem_map.mp hv
  rfl

theorem ehs_cost (after : List Name) :
    (ehs.map (ehSeg index payload pk after).cost).sum = subtreeHashes.length := by
  rw [← ehs_code index payload pk after]
  apply cost_eq_length
  intro n hn
  obtain ⟨l, _, rfl⟩ := List.mem_map.mp hn
  simp only [ehSeg, ehCost, ehCode]
  split_ifs <;> rfl

theorem evs_cost (after : List Name) :
    (evs.map (evSeg index payload pk after).cost).sum = subtreeReads.length := by
  rw [← evs_code index payload pk after]
  apply cost_eq_length
  intro n hn
  obtain ⟨l, _, rfl⟩ := List.mem_map.mp hn
  simp only [evSeg, evCost, evCode]
  split_ifs <;> rfl

theorem groups_to_ec (s : MachineState) (x : graph.Assignment) (cursor : ℕ)
    (done : GroupsDone index payload pk s x cursor) :
    EcInv index payload pk (ehs ++ (evs ++ [rc, rh])) s x cursor ecs := by
  obtain ⟨ctx, held⟩ := done
  refine ⟨ctx, held, ?_⟩
  intro l _ hn
  exact absurd (List.mem_map.mpr ⟨l, List.mem_finRange l, rfl⟩) hn

theorem ec_to_eh (after : List Name) (s : MachineState) (x : graph.Assignment) (cursor : ℕ)
    (h : EcInv index payload pk (ehs ++ after) s x cursor []) :
    EhInv index payload pk after s x cursor ehs := by
  obtain ⟨ctx, held, tagged⟩ := h
  refine ⟨by simpa only [List.nil_append] using ctx, held, ?_⟩
  intro l hl
  refine ⟨fun _ => tagged l hl (by simp), fun hn => ?_⟩
  exact absurd (List.mem_map.mpr ⟨l, List.mem_finRange l, rfl⟩) hn

theorem eh_to_ev (after : List Name) (s : MachineState) (x : graph.Assignment) (cursor : ℕ)
    (h : EhInv index payload pk (evs ++ after) s x cursor []) :
    EvInv index payload pk after s x cursor evs := by
  obtain ⟨ctx, _, facts⟩ := h
  refine ⟨by simpa only [List.nil_append] using ctx, ?_⟩
  intro l
  have mem : ev l ∈ evs := List.mem_map.mpr ⟨l, List.mem_finRange l, rfl⟩
  exact ⟨fun _ hl5 => (facts l hl5).2 (by simp), fun hn => absurd mem hn⟩

/-- The tree phase's registers and the subtree values, after the subtree phase. -/
def SubtreesDone (s : MachineState) (x : graph.Assignment) (cursor : ℕ) : Prop :=
  TreeCtx index payload pk s cursor [rc, rh] ∧ ∀ l : Fin 7, HoldsE s l (x (ev l).fin)

theorem ev_last (s : MachineState) (x : graph.Assignment) (cursor : ℕ)
    (h : EvInv index payload pk [rc, rh] s x cursor []) :
    SubtreesDone index payload pk s x cursor := by
  obtain ⟨ctx, facts⟩ := h
  exact ⟨by simpa only [List.nil_append] using ctx, fun l => (facts l).2 (by simp)⟩

/-- The whole subtree phase refines the reader over the subtree nodes. -/
theorem subtrees_refines (tail : Code)
    (K : graph.Assignment × ℕ → OracleComp (Spec paperParams) (Option Bool)) (c rest' : ℕ)
    (continuation : ∀ (u : MachineState) (y : graph.Assignment) (cursor' : ℕ),
      SubtreesDone index payload pk u y cursor' → Riscv.CodeAt u u.pc tail →
      ∀ left, rest' ≤ left → Riscv.Refines left u (K (y, cursor')) c)
    (s : MachineState) (x : graph.Assignment) (cursor fuel : ℕ)
    (done : GroupsDone index payload pk s x cursor)
    (located : Riscv.CodeAt s s.pc (subtrees ++ tail)) (bound : subtrees.length + rest' ≤ fuel) :
    Riscv.Refines fuel s (runNodes' index payload (ecs ++ (ehs ++ evs)) x cursor >>= K)
      (subtrees.length + c) := by
  have parts : subtrees = subtreeHashes ++ subtreeReads := rfl
  rw [parts] at located bound ⊢
  simp only [List.length_append] at bound ⊢
  simp only [List.append_assoc] at located
  simp only [runNodes'_append, bind_assoc]
  have step1 := sweep_refines index payload (ecSeg index payload pk (ehs ++ (evs ++ [rc, rh]))) ecs
    ecs_nodup (fun n hn => by
      obtain ⟨l, _, rfl⟩ := List.mem_map.mp hn
      exact ec_refines index payload pk _ l) (subtreeHashes ++ (subtreeReads ++ tail))
    (fun r => runNodes' index payload ehs r.1 r.2 >>= fun r' =>
      runNodes' index payload evs r'.1 r'.2 >>= K)
    (subtreeHashes.length + (subtreeReads.length + c)) (subtreeHashes.length + (subtreeReads.length + rest'))
    ?_ s x cursor fuel (groups_to_ec index payload pk s x cursor done) (by rw [ecs_code]; exact located)
    (by rw [ecs_code]; simp only [List.length_nil]; omega)
  · rw [ecs_cost, Nat.zero_add] at step1
    rw [Nat.add_assoc]
    exact step1
  intro v y cursor1 inv1 located1 left hleft
  dsimp only
  have step2 := sweep_refines index payload (ehSeg index payload pk (evs ++ [rc, rh])) ehs ehs_nodup
    (fun n hn => by
      obtain ⟨l, _, rfl⟩ := List.mem_map.mp hn
      exact eh_refines index payload pk _ l) (subtreeReads ++ tail)
    (fun r' => runNodes' index payload evs r'.1 r'.2 >>= K)
    (subtreeReads.length + c) (subtreeReads.length + rest') ?_ v y cursor1 left
    (ec_to_eh index payload pk _ v y cursor1 inv1)
    (by rw [ehs_code]; exact located1) (by rw [ehs_code]; omega)
  · rw [ehs_cost] at step2
    exact step2
  intro w z cursor2 inv2 located2 left2 hleft2
  dsimp only
  have step3 := sweep_refines index payload (evSeg index payload pk [rc, rh]) evs evs_nodup
    (fun n hn => by
      obtain ⟨l, _, rfl⟩ := List.mem_map.mp hn
      exact ev_refines index payload pk _ l) tail K c rest'
    (fun t y3 cursor3 inv3 located3 left3 hleft3 =>
      continuation t y3 cursor3 (ev_last index payload pk t y3 cursor3 inv3) located3 left3 hleft3)
    w z cursor2 left2 (eh_to_ev index payload pk _ w z cursor2 inv2)
    (by rw [evs_code]; exact located2) (by rw [evs_code]; exact hleft2)
  rw [evs_cost] at step3
  exact step3

end OptimalOTS.RiscvUpperProgram.Compact
