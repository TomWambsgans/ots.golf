import Submissions.RiscvUpper.CompactLevels

/-!
The tree phase of the compact image: the context shared by its three parts and the group phase.
`CompactSubtrees.lean` continues with the subtree phase and `CompactRoot.lean` with the root hash
and the decision.
-/

namespace OptimalOTS.RiscvUpperProgram.Compact

open RiscvZkvm.Rv64 Forest Forest.Name RiscvUpperForest.ForestVerifier OracleComp

set_option allowUnsafeReducibility true
attribute [local reducible] Forest.graph
attribute [local irreducible] Forest.fixedPositions Forest.fixedDigits

def groupAddr (j : ℕ) : Word := BitVec.ofNat 64 groupsBase + BitVec.ofNat 64 (groupSlot j)
def subtreeAddr (l : ℕ) : Word := BitVec.ofNat 64 subtreesBase + BitVec.ofNat 64 (subtreeSlot l)
def scratchAddr : Word := BitVec.ofNat 64 scratchBase

theorem groupAddr_aligned (j : ℕ) (_hj : j < 15) : alignToDword (groupAddr j) = groupAddr j := by
  apply (aligned_iff _).mpr
  simp only [groupAddr, groupsBase, groupSlot, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem subtreeAddr_aligned (l : ℕ) (_hl : l < 7) : alignToDword (subtreeAddr l) = subtreeAddr l := by
  apply (aligned_iff _).mpr
  simp only [subtreeAddr, subtreesBase, subtreeSlot, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem groupAddr_word (j i : ℕ) :
    groupAddr j + BitVec.ofNat 64 (8 * i) =
      BitVec.ofNat 64 groupsBase + BitVec.ofNat 64 (groupSlot j + 8 * i) := by
  rw [groupAddr, BitVec.ofNat_add, BitVec.add_assoc]

theorem subtreeAddr_word (l i : ℕ) :
    subtreeAddr l + BitVec.ofNat 64 (8 * i) =
      BitVec.ofNat 64 subtreesBase + BitVec.ofNat 64 (subtreeSlot l + 8 * i) := by
  rw [subtreeAddr, BitVec.ofNat_add, BitVec.add_assoc]

/-- Registers fixed throughout the tree phase. -/
structure TreeRegs (s : MachineState) : Prop where
  scratch : s.getReg .x18 = scratchAddr
  chains : s.getReg .x19 = BitVec.ofNat 64 chainsBase
  groups : s.getReg .x20 = BitVec.ofNat 64 groupsBase
  subtrees : s.getReg .x21 = BitVec.ofNat 64 subtreesBase
  call : s.getReg .x5 = Riscv.hashCall
  length : s.getReg .x11 = 400

variable (index : Idx paperParams) (payload : List Bool) (pk : PublicKey paperParams)

structure TreeCtx (s : MachineState) (cursor : ℕ) (rem : List Name) : Prop where
  context : ExecutionContext s index payload pk
  regs : TreeRegs s
  atCursor : CursorAt s cursor
  aligned : cursor % 128 = 0
  budget : cursor + (rem.map (consumedBits index)).sum ≤ 5248

def HoldsG (s : MachineState) (j : Fin 21) {w : ℕ} (v : BitVec w) : Prop := MemBits s (groupAddr j) v
def HoldsE (s : MachineState) (l : Fin 7) {w : ℕ} (v : BitVec w) : Prop := MemBits s (subtreeAddr l) v

/-- Final chain values, as the tree phase reads them. -/
def ChainsHeld (s : MachineState) (x : graph.Assignment) : Prop :=
  ∀ k : Fin 63, k.val < 36 → Holds s k (x (cv k 13).fin)

variable {index} {payload} {pk}

theorem TreeCtx.drop {s : MachineState} {cursor : ℕ} {n : Name} {rem : List Name}
    (ctx : TreeCtx index payload pk s cursor (n :: rem)) : TreeCtx index payload pk s cursor rem := by
  refine ⟨ctx.context, ctx.regs, ctx.atCursor, ctx.aligned, ?_⟩
  have := ctx.budget
  simp only [List.map_cons, List.sum_cons] at this
  omega

theorem TreeCtx.bounded {s : MachineState} {cursor : ℕ} {rem : List Name}
    (ctx : TreeCtx index payload pk s cursor rem) : cursor ≤ 5248 := by
  have := ctx.budget; omega

theorem TreeCtx.room {s : MachineState} {cursor : ℕ} {n : Name} {rem : List Name}
    (ctx : TreeCtx index payload pk s cursor (n :: rem)) (consumed : consumedBits index n = 128) :
    cursor + 128 ≤ 5248 := by
  have := ctx.budget
  simp only [List.map_cons, List.sum_cons, consumed] at this
  omega

/-- Writes at or above the group array preserve the tree context; the given registers survive. -/
theorem TreeCtx.step {s t : MachineState} {cursor : ℕ} {n : Name} {rem : List Name}
    (ctx : TreeCtx index payload pk s cursor (n :: rem)) (frame : FrameInputs s t)
    (regs : ∀ r, r = .x8 ∨ r = .x9 ∨ r = .x18 ∨ r = .x19 ∨ r = .x20 ∨ r = .x21 ∨ r = .x5 ∨ r = .x11 →
      t.getReg r = s.getReg r) :
    TreeCtx index payload pk t cursor rem := by
  have base := ctx.drop
  refine ⟨base.context.frameInputs frame (regs .x8 (by simp)), ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_,
    base.aligned, base.budget⟩
  · rw [regs .x18 (by simp)]; exact base.regs.scratch
  · rw [regs .x19 (by simp)]; exact base.regs.chains
  · rw [regs .x20 (by simp)]; exact base.regs.groups
  · rw [regs .x21 (by simp)]; exact base.regs.subtrees
  · rw [regs .x5 (by simp)]; exact base.regs.call
  · rw [regs .x11 (by simp)]; exact base.regs.length
  · unfold CursorAt
    rw [regs .x9 (by simp)]
    exact base.atCursor

theorem TreeCtx.read {s t : MachineState} {cursor : ℕ} {n : Name} {rem : List Name}
    (ctx : TreeCtx index payload pk s cursor (n :: rem)) (consumed : consumedBits index n = 128)
    (frame : FrameInputs s t)
    (regs : ∀ r, r = .x8 ∨ r = .x18 ∨ r = .x19 ∨ r = .x20 ∨ r = .x21 ∨ r = .x5 ∨ r = .x11 →
      t.getReg r = s.getReg r)
    (cursorReg : t.getReg .x9 = s.getReg .x9 + 16) :
    TreeCtx index payload pk t (cursor + 128) rem := by
  refine ⟨ctx.context.frameInputs frame (regs .x8 (by simp)), ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_,
    by have := ctx.aligned; omega, ?_⟩
  · rw [regs .x18 (by simp)]; exact ctx.regs.scratch
  · rw [regs .x19 (by simp)]; exact ctx.regs.chains
  · rw [regs .x20 (by simp)]; exact ctx.regs.groups
  · rw [regs .x21 (by simp)]; exact ctx.regs.subtrees
  · rw [regs .x5 (by simp)]; exact ctx.regs.call
  · rw [regs .x11 (by simp)]; exact ctx.regs.length
  · unfold CursorAt
    rw [cursorReg, ctx.atCursor, show (cursor + 128) / 8 = cursor / 8 + 16 by omega,
      BitVec.ofNat_add, ← BitVec.add_assoc]
    rfl
  · have := ctx.budget
    simp only [List.map_cons, List.sum_cons, consumed] at this
    omega

/-! ## Frames between the arrays -/

/-- Addresses below the group array (inputs, positions, chain slots) are untouched by writes to
scratch, groups and subtrees. -/
theorem holds_of_frame_groups {s t : MachineState} {k : Fin 63} (hk : k.val < 36) {w : ℕ}
    (v : BitVec w) (small : w ≤ 256)
    (frame : ∀ addr, addr.toNat < groupsBase → t.getMem addr = s.getMem addr)
    (held : Holds s k v) : Holds t k v := by
  apply memBits_of_word_frame s t _ v held
  intro i hi
  apply frame
  rw [aligned_bit_word _ ((aligned_iff _).mp (slotAddr_aligned k hk)) i
    (by rw [slotAddr_toNat k hk]; unfold chainsBase chainSlot; omega)]
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, slotAddr_toNat k hk]
  unfold chainsBase chainSlot groupsBase
  omega

theorem frameInputs_of_frame_groups {s t : MachineState}
    (frame : ∀ addr, addr.toNat < groupsBase → t.getMem addr = s.getMem addr) : FrameInputs s t := by
  intro addr below
  apply frame
  unfold chainsBase at below
  unfold groupsBase
  omega

/-! ## Group inputs -/

def gcs : List Name := (List.finRange 21).map gc
def ghs : List Name := (List.finRange 21).map gh
def gvs : List Name := (List.finRange 21).map gv
def ecs : List Name := (List.finRange 7).map ec
def ehs : List Name := (List.finRange 7).map eh
def evs : List Name := (List.finRange 7).map ev

theorem treeNodes_split : treeNodes = gcs ++ (ghs ++ (gvs ++ (ecs ++ (ehs ++ (evs ++ [rc, rh]))))) := by
  simp only [treeNodes, gcs, ghs, gvs, ecs, ehs, evs, List.append_assoc]

theorem gcs_nodup : gcs.Nodup := (List.nodup_finRange 21).map fun _ _ h => Name.gc.inj h
theorem ghs_nodup : ghs.Nodup := (List.nodup_finRange 21).map fun _ _ h => Name.gh.inj h
theorem gvs_nodup : gvs.Nodup := (List.nodup_finRange 21).map fun _ _ h => Name.gv.inj h
theorem ecs_nodup : ecs.Nodup := (List.nodup_finRange 7).map fun _ _ h => Name.ec.inj h
theorem ehs_nodup : ehs.Nodup := (List.nodup_finRange 7).map fun _ _ h => Name.eh.inj h
theorem evs_nodup : evs.Nodup := (List.nodup_finRange 7).map fun _ _ h => Name.ev.inj h

variable (index) (payload) (pk)

theorem evaluated_gc (j : Fin 21) : evaluated (fixedPositions index) (gc j) = decide (j.val < 12) := rfl
theorem evaluated_gh (j : Fin 21) : evaluated (fixedPositions index) (gh j) = decide (j.val < 12) := rfl
theorem evaluated_gv (j : Fin 21) : evaluated (fixedPositions index) (gv j) = decide (j.val < 12) := rfl
theorem disclosed_gv (j : Fin 21) :
    disclosed (fixedPositions index) (gv j) = decide (12 ≤ j.val ∧ j.val < 15) := rfl

theorem detVal_gv (j : Fin 21) (x : graph.Assignment) : detVal (.gv j) x = Forest.trunc (x (gh j).fin) := rfl

/-- The tagged group input of a processed node, in machine order. -/
def TaggedG (x : graph.Assignment) (j : Fin 21) : Prop :=
  x (gc j).fin = (tw (gh j) ++ cat3 (Forest.trunc (x (cv (chainOf j 0) 13).fin))
    (Forest.trunc (x (cv (chainOf j 1) 13).fin))
    (Forest.trunc (x (cv (chainOf j 2) 13).fin))).cast (graph_len_fin (gc j)).symm

theorem cursorStep_gc (j : Fin 21) (x : graph.Assignment) (cursor : ℕ) :
    cursorStep index payload x cursor (gc j) =
      if j.val < 12 then
        pure (Function.update x (gc j).fin
          ((tw (gh j) ++ cat3 (Forest.trunc (x (cv (chainOf j 0) 13).fin))
            (Forest.trunc (x (cv (chainOf j 1) 13).fin))
            (Forest.trunc (x (cv (chainOf j 2) 13).fin))).cast (graph_len_fin (gc j)).symm), cursor)
      else pure (Function.update x (gc j).fin 0, cursor) := by
  unfold cursorStep
  simp only [disclosed, Bool.false_eq_true, if_false, evaluated_gc, decide_eq_true_eq]
  split_ifs
  · rw [runOp_eq]
    simp only [evalName, map_pure, detVal_gc]
  · rfl

theorem cursorStep_gh (j : Fin 21) (x : graph.Assignment) (cursor : ℕ) :
    cursorStep index payload x cursor (gh j) =
      if j.val < 12 then
        (fun y => (Function.update x (gh j).fin (y.cast (graph_len_fin (gh j)).symm), cursor)) <$>
          hash paperParams (x (gc j).fin)
      else pure (Function.update x (gh j).fin 0, cursor) := by
  unfold cursorStep
  simp only [disclosed, Bool.false_eq_true, if_false, evaluated_gh, decide_eq_true_eq]
  split_ifs
  · rw [runOp_eq]
    simp only [evalName, Functor.map_map]
  · rfl

theorem cursorStep_gv (j : Fin 21) (x : graph.Assignment) (cursor : ℕ) :
    cursorStep index payload x cursor (gv j) =
      if 12 ≤ j.val ∧ j.val < 15 then
        pure (Function.update x (gv j).fin
          (ofBits (graph.len (gv j).fin) ((payload.drop cursor).take (graph.len (gv j).fin))),
          cursor + 128)
      else if j.val < 12 then
        pure (Function.update x (gv j).fin
          ((Forest.trunc (x (gh j).fin)).cast (graph_len_fin (gv j)).symm), cursor)
      else pure (Function.update x (gv j).fin 0, cursor) := by
  unfold cursorStep
  simp only [disclosed_gv, evaluated_gv, decide_eq_true_eq]
  split_ifs
  · rfl
  · rw [runOp_eq]
    simp only [evalName, map_pure, detVal_gv]
  · rfl

theorem consumedBits_gv (j : Fin 21) :
    consumedBits index (gv j) = if 12 ≤ j.val ∧ j.val < 15 then 128 else 0 := by
  rw [consumedBits_word, disclosed_gv]
  by_cases h : 12 ≤ j.val ∧ j.val < 15 <;> simp [h]

def GcInv (after : List Name) (s : MachineState) (x : graph.Assignment) (cursor : ℕ)
    (rem : List Name) : Prop :=
  TreeCtx index payload pk s cursor (rem ++ after) ∧ ChainsHeld s x ∧
  ∀ j : Fin 21, j.val < 12 → gc j ∉ rem → TaggedG x j

def gcSeg (after : List Name) : Segment := ⟨fun _ => [], fun _ => 0, GcInv index payload pk after⟩

theorem cv13_ne_gc (j : Fin 21) (k : Fin 63) : cv k 13 ≠ gc j := by simp

theorem gc_refines (after : List Name) (j : Fin 21) :
    (gcSeg index payload pk after).NodeRefines index payload (gc j) := by
  apply Segment.NodeRefines.ofPure
  · rfl
  · rfl
  · intro s x cursor rest _ inv r hr
    obtain ⟨ctx, held, tagged⟩ := inv
    rw [cursorStep_gc] at hr
    have value : ∃ v, r = (Function.update x (gc j).fin v, cursor) ∧
        (j.val < 12 → v = (tw (gh j) ++ cat3 (Forest.trunc (x (cv (chainOf j 0) 13).fin))
          (Forest.trunc (x (cv (chainOf j 1) 13).fin))
          (Forest.trunc (x (cv (chainOf j 2) 13).fin))).cast (graph_len_fin (gc j)).symm) := by
      split_ifs at hr with h
      · simp only [support_pure, Set.mem_singleton_iff] at hr
        exact ⟨_, hr, fun _ => rfl⟩
      · simp only [support_pure, Set.mem_singleton_iff] at hr
        exact ⟨_, hr, fun hj => absurd hj h⟩
    obtain ⟨v, rfl, hv⟩ := value
    refine ⟨ctx.drop, ?_, ?_⟩
    · intro k hk
      show Holds s k (Function.update x (gc j).fin v (cv k 13).fin)
      rw [Function.update_of_ne (fin_ne_of_ne (cv13_ne_gc j k))]
      exact held k hk
    · intro j' hj' notin
      unfold TaggedG
      dsimp only
      rw [Function.update_of_ne (fin_ne_of_ne (cv13_ne_gc j _)),
        Function.update_of_ne (fin_ne_of_ne (cv13_ne_gc j _)),
        Function.update_of_ne (fin_ne_of_ne (cv13_ne_gc j _))]
      by_cases same : j' = j
      · subst same
        rw [Function.update_self, hv hj']
      · rw [Function.update_of_ne (fin_ne_of_ne (fun h => same (Name.gc.inj h)))]
        exact tagged j' hj' (by simp only [List.mem_cons, not_or]; exact ⟨fun h => same (Name.gc.inj h), notin⟩)
  · intro x cursor
    by_cases h : j.val < 12
    · exact ⟨_, by rw [cursorStep_gc, if_pos h]⟩
    · exact ⟨_, by rw [cursorStep_gc, if_neg h]⟩


/-! ## Packing into the scratch buffer -/

theorem scratchAddr_aligned : scratchAddr.toNat % 8 = 0 := by decide
theorem scratchAddr_small : scratchAddr.toNat + 2048 < 2 ^ 64 := by decide

theorem scratch_half_access (off : ℕ) (hoff : off < 160) (aligned : off % 2 = 0) :
    isValidHalfwordAccess (scratchAddr + BitVec.ofNat 64 off) = true := by
  simp only [isValidHalfwordAccess, isAligned2, isValidMemAddr, MEM_START, MEM_END,
    INPUT_MEM_START, INPUT_MEM_END, RAM_MEM_START, RAM_MEM_END, scratchAddr, scratchBase,
    BitVec.toNat_add, BitVec.toNat_ofNat, Bool.and_eq_true, Bool.or_eq_true,
    decide_eq_true_eq, beq_iff_eq]
  omega

theorem scratch_word_access (off : ℕ) (hoff : off + 8 ≤ 160) (aligned : off % 8 = 0) :
    isValidDwordAccess (scratchAddr + BitVec.ofNat 64 off) = true := by
  have h := scratch_access (off / 8) (by omega)
  rw [show 8 * (off / 8) = off by omega] at h
  exact h

theorem scratch_ne_low (addr : Word) (low : addr.toNat < scratchBase) (off : ℕ) (hoff : off < 4096) :
    addr ≠ scratchAddr + BitVec.ofNat 64 off := by
  intro h
  have h' := congrArg BitVec.toNat h
  simp only [scratchAddr, BitVec.toNat_add, BitVec.toNat_ofNat] at h'
  unfold scratchBase at low h'
  omega

theorem copy_scratch_frame (s : MachineState) (src : Reg) (srcOff off : ℕ) (hs : src ≠ .x26)
    (hoff : off + 8 < 2048) (x18 : s.getReg .x18 = scratchAddr) (addr : Word)
    (low : addr.toNat < scratchBase) :
    ((copy128 src srcOff .x18 off).foldl execInstrBr s).getMem addr = s.getMem addr := by
  rw [copy128_getMem _ _ _ _ _ hs (by decide) (by decide), signExtend12_nonnegative (off + 8) hoff,
    signExtend12_nonnegative off (by omega), x18,
    if_neg (scratch_ne_low addr low _ (by omega)), if_neg (scratch_ne_low addr low _ (by omega))]

theorem tag_scratch_frame (s : MachineState) (tag : BitVec 16) (off : ℕ) (hoff : off < 2048)
    (literal : (literalValue tag.toNat).truncate 16 = tag) (x18 : s.getReg .x18 = scratchAddr)
    (addr : Word) (low : addr.toNat < scratchBase) :
    ((writeTag tag off).foldl execInstrBr s).getMem addr = s.getMem addr := by
  apply writeTag_frame _ _ _ _ hoff literal
  rw [x18]
  intro h
  have h' := congrArg BitVec.toNat h
  rw [alignToDword_toNat] at h'
  simp only [scratchAddr, BitVec.toNat_add, BitVec.toNat_ofNat] at h'
  unfold scratchBase at low h'
  omega

/-- Values stored below the scratch buffer survive writes into it. -/
theorem memBits_frame_low {w : ℕ} {s t : MachineState} {base : Word} {v : BitVec w}
    (low : base.toNat + w / 8 < scratchBase)
    (frame : ∀ addr : Word, addr.toNat < scratchBase → t.getMem addr = s.getMem addr)
    (held : MemBits s base v) : MemBits t base v := by
  apply memBits_of_word_frame s t base v held
  intro i hi
  apply frame
  rw [alignToDword_toNat]
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  unfold scratchBase at low ⊢
  omega

theorem scratch_append {width : ℕ} (s : MachineState) (src : Reg) (srcOff off : ℕ)
    (lo : BitVec width) (hi : BitVec 128) (bounded : width ≤ 896) (wordAligned : width % 64 = 0)
    (hoff : off = width / 8) (hs : src ≠ .x26) (hsrc : srcOff + 8 < 2048)
    (x18 : s.getReg .x18 = scratchAddr)
    (sourceAligned : alignToDword (s.getReg src + BitVec.ofNat 64 srcOff) =
      s.getReg src + BitVec.ofNat 64 srcOff)
    (preceding : MemBits s scratchAddr lo)
    (source : MemBits s (s.getReg src + BitVec.ofNat 64 srcOff) hi) :
    MemBits ((copy128 src srcOff .x18 off).foldl execInstrBr s) scratchAddr (hi ++ lo) := by
  subst hoff
  have zero : s.getReg .x18 + BitVec.ofNat 64 0 = scratchAddr := by
    rw [x18]; exact BitVec.add_zero _
  have h := copy_append s src srcOff 0 lo hi bounded wordAligned hs hsrc (by omega) (by decide)
    (by rw [x18]; exact scratchAddr_aligned) (by rw [x18]; exact scratchAddr_small) sourceAligned
    (by rw [zero]; exact preceding) source
  rw [zero, Nat.zero_add] at h
  exact h

theorem scratch_tag {width : ℕ} (s : MachineState) (off : ℕ) (value : BitVec width)
    (tag : BitVec 16) (bounded : width ≤ 896) (wordAligned : width % 64 = 0)
    (hoff : off = width / 8) (literal : (literalValue tag.toNat).truncate 16 = tag)
    (x18 : s.getReg .x18 = scratchAddr) (represented : MemBits s scratchAddr value) :
    MemBits ((writeTag tag off).foldl execInstrBr s) scratchAddr (tag ++ value) := by
  subst hoff
  have zero : s.getReg .x18 + BitVec.ofNat 64 0 = scratchAddr := by
    rw [x18]; exact BitVec.add_zero _
  have h := tag_append s 0 value tag bounded wordAligned literal (by omega) (by decide)
    (by rw [x18]; exact scratchAddr_aligned) (by rw [x18]; exact scratchAddr_small)
    (by rw [zero]; exact represented)
  rw [zero, Nat.zero_add] at h
  exact h

theorem tag_scratch_ready (s : MachineState) (tag : BitVec 16) (off : ℕ) (hoff : off < 160)
    (aligned : off % 2 = 0) (x18 : s.getReg .x18 = scratchAddr) :
    Riscv.LinearReady s (writeTag tag off) := by
  apply (constant_ready _ _ _).append
  refine ⟨rfl, ?_, trivial⟩
  change isValidHalfwordAccess (_ + signExtend12 (BitVec.ofNat 12 off)) = true
  rw [signExtend12_nonnegative off (by omega), constant_preserves _ .x26 .x18 _ (by decide), x18]
  exact scratch_half_access off hoff aligned

/-- The three-word input macro: it packs `tag ++ (va ++ (vb ++ vc))` into scratch, changes only
the two temporaries, and leaves memory below the scratch buffer alone. -/
theorem tripleInput_effect (s : MachineState) (src : Reg) (a b c tagN : ℕ)
    (va vb vc : BitVec 128) (hs : src ≠ .x26) (hs' : src ≠ .x27)
    (ha : a + 8 < 2048) (hb : b + 8 < 2048) (hc : c + 8 < 2048)
    (literal : (literalValue (BitVec.ofNat 16 tagN).toNat).truncate 16 = BitVec.ofNat 16 tagN)
    (x18 : s.getReg .x18 = scratchAddr) (low : (s.getReg src).toNat + 4096 ≤ scratchBase)
    (access : ∀ off, off = a ∨ off = a + 8 ∨ off = b ∨ off = b + 8 ∨ off = c ∨ off = c + 8 →
      isValidDwordAccess (s.getReg src + BitVec.ofNat 64 off) = true)
    (aligned : ∀ off, off = a ∨ off = b ∨ off = c →
      alignToDword (s.getReg src + BitVec.ofNat 64 off) = s.getReg src + BitVec.ofNat 64 off)
    (srcA : MemBits s (s.getReg src + BitVec.ofNat 64 a) va)
    (srcB : MemBits s (s.getReg src + BitVec.ofNat 64 b) vb)
    (srcC : MemBits s (s.getReg src + BitVec.ofNat 64 c) vc) :
    Riscv.LinearReady s (tripleInput src a b c tagN) ∧
    (∀ r, r ≠ .x26 → r ≠ .x27 →
      ((tripleInput src a b c tagN).foldl execInstrBr s).getReg r = s.getReg r) ∧
    (∀ addr : Word, addr.toNat < scratchBase →
      ((tripleInput src a b c tagN).foldl execInstrBr s).getMem addr = s.getMem addr) ∧
    MemBits ((tripleInput src a b c tagN).foldl execInstrBr s) scratchAddr
      (BitVec.ofNat 16 tagN ++ (va ++ (vb ++ vc))) := by
  have lowWord : ∀ off, off < 2048 →
      (s.getReg src + BitVec.ofNat 64 off).toNat + 128 / 8 < scratchBase := by
    intro off hoff
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    unfold scratchBase at low ⊢
    omega
  have unfolded : (tripleInput src a b c tagN).foldl execInstrBr s =
      (writeTag (BitVec.ofNat 16 tagN) 48).foldl execInstrBr
        ((copy128 src a .x18 32).foldl execInstrBr
          ((copy128 src b .x18 16).foldl execInstrBr
            ((copy128 src c .x18 0).foldl execInstrBr s))) := by
    simp only [tripleInput, List.foldl_append]
  -- first copy: `c` at offset 0
  have r1 : Riscv.LinearReady s (copy128 src c .x18 0) := by
    apply copy128_ready s src .x18 c 0 hs (by decide) (by decide)
    · rw [signExtend12_nonnegative c (by omega)]; exact access c (by simp)
    · rw [signExtend12_nonnegative (c + 8) hc]; exact access (c + 8) (by simp)
    · rw [signExtend12_nonnegative 0 (by decide), x18]
      exact scratch_word_access 0 (by decide) (by decide)
    · rw [signExtend12_nonnegative (0 + 8) (by decide), x18]
      exact scratch_word_access (0 + 8) (by decide) (by decide)
  set s1 := (copy128 src c .x18 0).foldl execInstrBr s with hs1
  have g1 : ∀ r, r ≠ .x26 → r ≠ .x27 → s1.getReg r = s.getReg r := fun r h26 h27 =>
    copy128_reg s src .x18 r c 0 h26 h27
  have f1 : ∀ addr : Word, addr.toNat < scratchBase → s1.getMem addr = s.getMem addr :=
    fun addr low' => copy_scratch_frame s src c 0 hs (by decide) x18 addr low'
  have m1 : MemBits s1 scratchAddr vc := by
    have h := copy128_memBits s src .x18 c 0 hs (by decide) (by decide) hc (by decide)
      (aligned c (by simp))
      (by rw [x18, BitVec.add_zero]; exact (aligned_iff _).mpr scratchAddr_aligned) vc srcC
    rw [x18, BitVec.add_zero] at h
    exact h
  have x18₁ : s1.getReg .x18 = scratchAddr := by rw [g1 .x18 (by decide) (by decide), x18]
  have src₁ : s1.getReg src = s.getReg src := g1 src hs hs'
  -- second copy: `b` at offset 16
  have r2 : Riscv.LinearReady s1 (copy128 src b .x18 16) := by
    apply copy128_ready s1 src .x18 b 16 hs (by decide) (by decide)
    · rw [signExtend12_nonnegative b (by omega), src₁]; exact access b (by simp)
    · rw [signExtend12_nonnegative (b + 8) hb, src₁]; exact access (b + 8) (by simp)
    · rw [signExtend12_nonnegative 16 (by decide), x18₁]
      exact scratch_word_access 16 (by decide) (by decide)
    · rw [signExtend12_nonnegative (16 + 8) (by decide), x18₁]
      exact scratch_word_access (16 + 8) (by decide) (by decide)
  set s2 := (copy128 src b .x18 16).foldl execInstrBr s1 with hs2
  have g2 : ∀ r, r ≠ .x26 → r ≠ .x27 → s2.getReg r = s1.getReg r := fun r h26 h27 =>
    copy128_reg s1 src .x18 r b 16 h26 h27
  have f2 : ∀ addr : Word, addr.toNat < scratchBase → s2.getMem addr = s1.getMem addr :=
    fun addr low' => copy_scratch_frame s1 src b 16 hs (by decide) x18₁ addr low'
  have m2 : MemBits s2 scratchAddr (vb ++ vc) := by
    apply scratch_append s1 src b 16 vc vb (by decide) (by decide) rfl hs hb x18₁
    · rw [src₁]; exact aligned b (by simp)
    · exact m1
    · rw [src₁]; exact memBits_frame_low (lowWord b (by omega)) f1 srcB
  have x18₂ : s2.getReg .x18 = scratchAddr := by rw [g2 .x18 (by decide) (by decide), x18₁]
  have src₂ : s2.getReg src = s.getReg src := by rw [g2 src hs hs', src₁]
  -- third copy: `a` at offset 32
  have r3 : Riscv.LinearReady s2 (copy128 src a .x18 32) := by
    apply copy128_ready s2 src .x18 a 32 hs (by decide) (by decide)
    · rw [signExtend12_nonnegative a (by omega), src₂]; exact access a (by simp)
    · rw [signExtend12_nonnegative (a + 8) ha, src₂]; exact access (a + 8) (by simp)
    · rw [signExtend12_nonnegative 32 (by decide), x18₂]
      exact scratch_word_access 32 (by decide) (by decide)
    · rw [signExtend12_nonnegative (32 + 8) (by decide), x18₂]
      exact scratch_word_access (32 + 8) (by decide) (by decide)
  set s3 := (copy128 src a .x18 32).foldl execInstrBr s2 with hs3
  have g3 : ∀ r, r ≠ .x26 → r ≠ .x27 → s3.getReg r = s2.getReg r := fun r h26 h27 =>
    copy128_reg s2 src .x18 r a 32 h26 h27
  have f3 : ∀ addr : Word, addr.toNat < scratchBase → s3.getMem addr = s2.getMem addr :=
    fun addr low' => copy_scratch_frame s2 src a 32 hs (by decide) x18₂ addr low'
  have m3 : MemBits s3 scratchAddr (va ++ (vb ++ vc)) := by
    apply scratch_append s2 src a 32 (vb ++ vc) va (by decide) (by decide) rfl hs ha x18₂
    · rw [src₂]; exact aligned a (by simp)
    · exact m2
    · rw [src₂]
      exact memBits_frame_low (lowWord a (by omega)) (fun addr low' => (f2 addr low').trans (f1 addr low')) srcA
  have x18₃ : s3.getReg .x18 = scratchAddr := by rw [g3 .x18 (by decide) (by decide), x18₂]
  -- the tag at offset 48
  have r4 : Riscv.LinearReady s3 (writeTag (BitVec.ofNat 16 tagN) 48) :=
    tag_scratch_ready s3 _ 48 (by decide) (by decide) x18₃
  have g4 : ∀ r, r ≠ .x26 →
      ((writeTag (BitVec.ofNat 16 tagN) 48).foldl execInstrBr s3).getReg r = s3.getReg r :=
    fun r h26 => writeTag_register s3 _ _ r h26
  have f4 : ∀ addr : Word, addr.toNat < scratchBase →
      ((writeTag (BitVec.ofNat 16 tagN) 48).foldl execInstrBr s3).getMem addr = s3.getMem addr :=
    fun addr low' => tag_scratch_frame s3 _ 48 (by decide) literal x18₃ addr low'
  have m4 : MemBits ((writeTag (BitVec.ofNat 16 tagN) 48).foldl execInstrBr s3) scratchAddr
      (BitVec.ofNat 16 tagN ++ (va ++ (vb ++ vc))) :=
    scratch_tag s3 48 (va ++ (vb ++ vc)) _ (by decide) (by decide) rfl literal x18₃ m3
  -- assemble
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold tripleInput
    refine Riscv.LinearReady.append (Riscv.LinearReady.append (Riscv.LinearReady.append r1 r2) ?_) ?_
    · rw [List.foldl_append]; exact r3
    · rw [List.foldl_append, List.foldl_append]; exact r4
  · intro r h26 h27
    rw [unfolded, g4 r h26, g3 r h26 h27, g2 r h26 h27, g1 r h26 h27]
  · intro addr low'
    rw [unfolded, f4 addr low', f3 addr low', f2 addr low', f1 addr low']
  · rw [unfolded]; exact m4

/-! ## Group hashes -/

def groupLin (j : ℕ) : Code :=
  tripleInput .x19 (chainSlot (3 * j)) (chainSlot (3 * j + 1)) (chainSlot (3 * j + 2)) (2730 + j) ++
  [.ADDI .x10 .x18 0, .ADDI .x12 .x20 (BitVec.ofNat 12 (groupSlot j))]

theorem groupBlock_parts (j : ℕ) : groupBlock j = groupLin j ++ [Instr.ECALL] := by
  simp [groupBlock, groupLin, List.append_assoc]

theorem groupBlock_length (j : ℕ) : (groupBlock j).length = (groupLin j).length + 1 := by
  rw [groupBlock_parts]; simp

theorem gc_len (j : Fin 21) : graph.len (gc j).fin = 400 := graph_len_fin (gc j)
theorem gh_len_le (j : Fin 21) : graph.len (gh j).fin ≤ 256 := by
  rw [graph_len_fin]; norm_num [Name.len]

theorem groupTag_literal (j : Fin 21) :
    (literalValue (BitVec.ofNat 16 (2730 + j.val)).toNat).truncate 16 = BitVec.ofNat 16 (2730 + j.val) :=
  nodeTag_literal (.gh j)

theorem groupAddr_access (j : ℕ) (hj : j < 15) (i : ℕ) (hi : i < 4) :
    isValidDwordAccess (groupAddr j + BitVec.ofNat 64 (8 * i)) = true := by
  rw [groupAddr_word]
  exact group_access j i hj hi

theorem cat3_assoc (p q r : BitVec 128) : cat3 p q r = p ++ (q ++ r) := by
  simp only [cat3, BitVec.append_assoc, BitVec.cast_eq]

/-- The linear part of a group block loads the exact 400-bit group input into scratch and points
the hash at it and at the group's slot. -/
theorem groupLin_effect (s : MachineState) (j : Fin 21) (hj : j.val < 12) (regs : TreeRegs s)
    (x : graph.Assignment) (held : ChainsHeld s x) (tagged : TaggedG x j) :
    Riscv.LinearReady s (groupLin j) ∧
    ((groupLin j).foldl execInstrBr s).getReg .x10 = scratchAddr ∧
    ((groupLin j).foldl execInstrBr s).getReg .x12 = groupAddr j ∧
    (∀ r, r ≠ .x10 → r ≠ .x12 → r ≠ .x26 → r ≠ .x27 →
      ((groupLin j).foldl execInstrBr s).getReg r = s.getReg r) ∧
    (∀ addr : Word, addr.toNat < scratchBase →
      ((groupLin j).foldl execInstrBr s).getMem addr = s.getMem addr) ∧
    MemBits ((groupLin j).foldl execInstrBr s) scratchAddr (x (gc j).fin) := by
  have h0 : (chainOf j 0).val < 36 := by show 3 * j.val + 0 < 36; omega
  have h1 : (chainOf j 1).val < 36 := by show 3 * j.val + 1 < 36; omega
  have h2 : (chainOf j 2).val < 36 := by show 3 * j.val + 2 < 36; omega
  have slot : ∀ k, k < 36 → chainSlot k + 8 < 2048 := by intro k hk; unfold chainSlot; omega
  have source : ∀ k : Fin 63, k.val < 36 →
      MemBits s (s.getReg .x19 + BitVec.ofNat 64 (chainSlot k)) (Forest.trunc (x (cv k 13).fin)) := by
    intro k hk
    rw [regs.chains]
    exact (held k hk).trunc
  have access : ∀ off, off = chainSlot (chainOf j 0) ∨ off = chainSlot (chainOf j 0) + 8 ∨
      off = chainSlot (chainOf j 1) ∨ off = chainSlot (chainOf j 1) + 8 ∨
      off = chainSlot (chainOf j 2) ∨ off = chainSlot (chainOf j 2) + 8 →
      isValidDwordAccess (s.getReg .x19 + BitVec.ofNat 64 off) = true := by
    intro off hoff
    rw [regs.chains]
    rcases hoff with h | h | h | h | h | h <;> subst h
    · simpa only [Nat.mul_zero, Nat.add_zero] using chain_access _ 0 h0 (by decide)
    · simpa only [Nat.mul_one] using chain_access _ 1 h0 (by decide)
    · simpa only [Nat.mul_zero, Nat.add_zero] using chain_access _ 0 h1 (by decide)
    · simpa only [Nat.mul_one] using chain_access _ 1 h1 (by decide)
    · simpa only [Nat.mul_zero, Nat.add_zero] using chain_access _ 0 h2 (by decide)
    · simpa only [Nat.mul_one] using chain_access _ 1 h2 (by decide)
  have aligned : ∀ off, off = chainSlot (chainOf j 0) ∨ off = chainSlot (chainOf j 1) ∨
      off = chainSlot (chainOf j 2) →
      alignToDword (s.getReg .x19 + BitVec.ofNat 64 off) = s.getReg .x19 + BitVec.ofNat 64 off := by
    intro off hoff
    rw [regs.chains]
    rcases hoff with h | h | h <;> subst h
    · exact slotAddr_aligned _ h0
    · exact slotAddr_aligned _ h1
    · exact slotAddr_aligned _ h2
  have low : (s.getReg .x19).toNat + 4096 ≤ scratchBase := by rw [regs.chains]; decide
  obtain ⟨ready, tregs, frame, packed⟩ := tripleInput_effect s .x19 (chainSlot (chainOf j 0))
    (chainSlot (chainOf j 1)) (chainSlot (chainOf j 2)) (2730 + j.val) _ _ _ (by decide) (by decide)
    (slot _ h0) (slot _ h1) (slot _ h2) (groupTag_literal j) regs.scratch low access aligned
    (source _ h0) (source _ h1) (source _ h2)
  have same : tripleInput .x19 (chainSlot (chainOf j 0)) (chainSlot (chainOf j 1))
      (chainSlot (chainOf j 2)) (2730 + j.val) =
      tripleInput .x19 (chainSlot (3 * j.val)) (chainSlot (3 * j.val + 1))
        (chainSlot (3 * j.val + 2)) (2730 + j.val) := rfl
  rw [same] at ready tregs frame packed
  generalize hu : (tripleInput .x19 (chainSlot (3 * j.val)) (chainSlot (3 * j.val + 1))
    (chainSlot (3 * j.val + 2)) (2730 + j.val)).foldl execInstrBr s = u at tregs frame packed
  have hgroup : groupSlot j < 2048 := by unfold groupSlot; omega
  have zero : signExtend12 (0 : BitVec 12) = 0#64 := by decide
  have unfolded : (groupLin j).foldl execInstrBr s =
      [Instr.ADDI .x10 .x18 0, .ADDI .x12 .x20 (BitVec.ofNat 12 (groupSlot j))].foldl execInstrBr u := by
    simp only [groupLin, List.foldl_append, hu]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ready.append ⟨rfl, trivial, rfl, trivial, trivial⟩
  · rw [unfolded]
    simp only [List.foldl_cons, List.foldl_nil, execInstrBr, zero,
      MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ .x12 .x10 _ (by decide),
      MachineState.getReg_setReg_eq (by decide : Reg.x10 ≠ .x0)]
    rw [tregs .x18 (by decide) (by decide), regs.scratch, BitVec.add_zero]
  · rw [unfolded]
    simp only [List.foldl_cons, List.foldl_nil, execInstrBr,
      signExtend12_nonnegative (groupSlot j) hgroup, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x12 ≠ .x0),
      MachineState.getReg_setReg_ne _ .x10 .x20 _ (by decide)]
    rw [tregs .x20 (by decide) (by decide), regs.groups]
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
    have value : MemBits u scratchAddr (x (gc j).fin) := by
      rw [tagged]
      apply (memBits_cast _ _ _ _).mpr
      rw [cat3_assoc]
      exact packed
    exact memBits_of_mem_eq rfl value

/-! ## Frames around group slots -/

theorem groupAddr_toNat (j : ℕ) (hj : j < 15) : (groupAddr j).toNat = groupsBase + groupSlot j := by
  simp only [groupAddr, groupsBase, groupSlot, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem groupAddr_word_ne (j j' : ℕ) (hj : j < 15) (hj' : j' < 15) (i i' : ℕ) (hi : i < 4)
    (hi' : i' < 4) (different : j ≠ j') :
    groupAddr j + BitVec.ofNat 64 (8 * i) ≠ groupAddr j' + BitVec.ofNat 64 (8 * i') := by
  intro h
  have h' := congrArg BitVec.toNat h
  simp only [groupAddr, groupsBase, groupSlot, BitVec.toNat_add, BitVec.toNat_ofNat] at h'
  omega

theorem group_ne_low (addr : Word) (low : addr.toNat < groupsBase) (j : ℕ) (i : ℕ) (hj : j < 15)
    (hi : i < 4) : addr ≠ groupAddr j + BitVec.ofNat 64 (8 * i) := by
  intro h
  have h' := congrArg BitVec.toNat h
  simp only [groupAddr, groupsBase, groupSlot, BitVec.toNat_add, BitVec.toNat_ofNat] at h'
  unfold groupsBase at low
  omega

theorem groupAddr_low (j : ℕ) (hj : j < 15) (i : ℕ) (hi : i < 4) :
    (groupAddr j + BitVec.ofNat 64 (8 * i)).toNat < scratchBase := by
  simp only [groupAddr, groupsBase, groupSlot, scratchBase, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- Writes into one group slot leave the other group slots alone. -/
theorem HoldsG.frame {s t : MachineState} {j j' : Fin 21} (hj : j.val < 15) (hj' : j'.val < 15)
    (different : j' ≠ j) {w : ℕ} (v : BitVec w) (small : w ≤ 256)
    (frame : ∀ addr, (∀ i, i < 4 → addr ≠ groupAddr j + BitVec.ofNat 64 (8 * i)) →
      addr.toNat < scratchBase → t.getMem addr = s.getMem addr)
    (held : HoldsG s j' v) : HoldsG t j' v := by
  apply memBits_of_word_frame s t _ v held
  intro i hi
  rw [aligned_bit_word _ ((aligned_iff _).mp (groupAddr_aligned j' hj')) i
    (by rw [groupAddr_toNat j' hj']; unfold groupsBase groupSlot; omega)]
  apply frame
  · intro i' hi'
    exact groupAddr_word_ne j' j hj' hj (i / 64) i' (by omega) hi' (fun h => different (Fin.ext h))
  · exact groupAddr_low j' hj' (i / 64) (by omega)

/-- The value of a node truncates to its first machine word. -/
theorem memBits_trunc {s : MachineState} {base : Word} {n : Name} {x : graph.Assignment}
    (held : MemBits s base (x n.fin)) : MemBits s base (Forest.trunc (x n.fin)) := by
  have bound : 0 + 128 ≤ graph.len n.fin := by
    rw [graph_len_fin]
    exact node_length_positive n
  have h := memBits_extract (start := 0) (len := 128) held (by decide) bound
  have he : (x n.fin).extractLsb' 0 128 = Forest.trunc (x n.fin) := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp [Forest.trunc, hi]
  rw [show base + BitVec.ofNat 64 (0 / 8) = base from BitVec.add_zero _, he] at h
  exact h

/-! ## The group hash segment -/

def ghCode : Name → Code
  | .gh j => if j.val < 12 then groupBlock j.val else []
  | _ => []

def ghCost : Name → ℕ
  | .gh j => if j.val < 12 then (groupBlock j.val).length else 0
  | _ => 0

/-- Pending groups hold their tagged input in the assignment; hashed groups hold the answer. -/
def GhInv (after : List Name) (s : MachineState) (x : graph.Assignment) (cursor : ℕ)
    (rem : List Name) : Prop :=
  TreeCtx index payload pk s cursor (rem ++ after) ∧ ChainsHeld s x ∧
  ∀ j : Fin 21, j.val < 12 → (gh j ∈ rem → TaggedG x j) ∧ (gh j ∉ rem → HoldsG s j (x (gh j).fin))

def ghSeg (after : List Name) : Segment := ⟨ghCode, ghCost, GhInv index payload pk after⟩

theorem gh_refines (after : List Name) (j : Fin 21) :
    (ghSeg index payload pk after).NodeRefines index payload (gh j) := by
  by_cases hj : j.val < 12
  · intro s x cursor rest tail K c budget fuel fresh inv located0 bound continuation
    obtain ⟨ctx, held, facts⟩ := inv
    have code : ghCode (gh j) = groupBlock j := by simp [ghCode, hj]
    have cost : ghCost (gh j) = (groupBlock j).length := by simp [ghCost, hj]
    change Riscv.CodeAt s s.pc (ghCode (gh j) ++ tail) at located0
    change (ghCode (gh j)).length + budget ≤ fuel at bound
    rw [code] at located0 bound
    change Riscv.Refines fuel s _ (ghCost (gh j) + c)
    rw [cost, cursorStep_gh, if_pos hj]
    have located := located0
    rw [groupBlock_parts, List.append_assoc] at located
    rw [groupBlock_length] at bound
    obtain ⟨ready, w10, w12, wRegs, wFrame, wValue⟩ :=
      groupLin_effect s j hj ctx.regs x held ((facts j hj).1 (by simp))
    set w := (groupLin j).foldl execInstrBr s with hw
    have wPc : w.pc = s.pc + BitVec.ofNat 64 (4 * (groupLin j).length) :=
      Riscv.linear_fold_pc s _ ready
    have wCode : Riscv.CodeAt w w.pc ([Instr.ECALL] ++ tail) := by
      rw [wPc]; exact located.append_right.code_eq (Riscv.fold_code s _)
    have wCodeEq : w.code = s.code := Riscv.fold_code s _
    have wFetch : w.code w.pc = some .ECALL := wCode.head
    have wCall : w.getReg .x5 = Riscv.hashCall := by
      rw [wRegs .x5 (by decide) (by decide) (by decide) (by decide)]; exact ctx.regs.call
    have wLen : w.getReg .x11 = 400 := by
      rw [wRegs .x11 (by decide) (by decide) (by decide) (by decide)]; exact ctx.regs.length
    have hj15 : j.val < 15 := by omega
    have wValid : Riscv.hashArgumentsValid w = true := by
      simp only [Riscv.hashArgumentsValid, w10, w12, wLen, Bool.and_eq_true]
      refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
      · show isValidOutputRange scratchAddr 50 = true
        exact scratch_output_range_50
      · have h := groupAddr_access j hj15 0 (by decide)
        rwa [Nat.mul_zero, BitVec.add_zero] at h
      · have h := groupAddr_access j hj15 1 (by decide)
        rwa [show BitVec.ofNat 64 (8 * 1) = (8 : Word) from rfl] at h
      · have h := groupAddr_access j hj15 2 (by decide)
        rwa [show BitVec.ofNat 64 (8 * 2) = (16 : Word) from rfl] at h
      · have h := groupAddr_access j hj15 3 (by decide)
        rwa [show BitVec.ofNat 64 (8 * 3) = (24 : Word) from rfl] at h
    have wInput : Riscv.hashInput w = ⟨graph.len (gc j).fin, x (gc j).fin⟩ :=
      hashInput_of_memBits w10 (by rw [wLen, gc_len]; rfl) wValue
    have blocks : blockCost paperParams (graph.len (gc j).fin) = 1 := by rw [gc_len]; decide
    rw [groupBlock_length, show (groupLin j).length + 1 + c = (groupLin j).length + (1 + c) by omega,
      show fuel = (groupLin j).length + ((fuel - (groupLin j).length - 1) + 1) by omega]
    apply Riscv.Refines.linear _ located.append_left ready
    rw [← hw]
    simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp_apply, pure_bind]
    have step := Riscv.Refines.hash (fuel := fuel - (groupLin j).length - 1) wFetch wCall wValid
      (k := fun y => K (Function.update x (gh j).fin (y.cast (graph_len_fin (gh j)).symm), cursor))
      (c := c) ?_
    · rw [wInput, blocks] at step
      exact step
    intro y
    set v := Riscv.writeHash w y with hv
    have vRegs : ∀ r, r ≠ .x10 → r ≠ .x12 → r ≠ .x26 → r ≠ .x27 → v.getReg r = s.getReg r := by
      intro r h10 h12 h26 h27
      rw [hv, writeHash_regs, wRegs r h10 h12 h26 h27]
    have groupFrame : ∀ addr, (∀ i, i < 4 → addr ≠ groupAddr j + BitVec.ofNat 64 (8 * i)) →
        addr.toNat < scratchBase → v.getMem addr = s.getMem addr := by
      intro addr outside low
      rw [hv, writeHash_frame _ _ _ (by rw [w12]; exact outside), wFrame addr low]
    have lowFrame : ∀ addr : Word, addr.toNat < groupsBase → v.getMem addr = s.getMem addr := by
      intro addr low
      apply groupFrame addr (fun i hi => group_ne_low addr low j i hj15 hi)
      unfold groupsBase at low
      unfold scratchBase
      omega
    have vPc : v.pc = s.pc + BitVec.ofNat 64 (4 * (groupBlock j).length) := by
      rw [hv, writeHash_pc, wPc, groupBlock_length,
        show (4 : Word) = BitVec.ofNat 64 4 from rfl, pcAdd,
        show 4 * (groupLin j).length + 4 = 4 * ((groupLin j).length + 1) by omega]
    have vCode : v.code = s.code := by rw [hv, writeHash_code, wCodeEq]
    have vLocated : Riscv.CodeAt v v.pc tail := by
      rw [vPc]; exact located0.append_right.code_eq vCode
    have answer : HoldsG v j ((y.cast (graph_len_fin (gh j)).symm : BitVec (graph.len (gh j).fin))) := by
      unfold HoldsG
      apply (memBits_cast _ _ _ _).mpr
      have h := writeHash_memBits w y (by rw [w12]; exact groupAddr_aligned j hj15)
      rw [w12] at h
      exact h
    apply continuation v (Function.update x (gh j).fin (y.cast (graph_len_fin (gh j)).symm), cursor)
      ?_ ?_ vLocated (fuel - (groupLin j).length - 1) (by omega)
    · rw [cursorStep_gh, if_pos hj, support_map]
      exact ⟨y, mem_support_hash _ y, rfl⟩
    · refine ⟨ctx.step (frameInputs_of_frame_groups lowFrame) ?_, ?_, ?_⟩
      · intro r hr
        apply vRegs r <;> rintro rfl <;> simp at hr
      · intro k hk
        show Holds v k (Function.update x (gh j).fin _ (cv k 13).fin)
        rw [Function.update_of_ne (fin_ne_of_ne (by simp : cv k 13 ≠ gh j))]
        exact holds_of_frame_groups hk _ (cv_len_le k 13) lowFrame (held k hk)
      · intro j' hj'
        dsimp only
        by_cases same : j' = j
        · subst same
          refine ⟨fun h => absurd h fresh, fun _ => ?_⟩
          rw [Function.update_self]
          exact answer
        · have neGh : (gh j').fin ≠ (gh j).fin := fin_ne_of_ne (fun h => same (Name.gh.inj h))
          refine ⟨fun hmem => ?_, fun hnot => ?_⟩
          · have t := (facts j' hj').1 (by simp [hmem])
            unfold TaggedG at t ⊢
            rw [Function.update_of_ne (fin_ne_of_ne (by simp : gc j' ≠ gh j)),
              Function.update_of_ne (fin_ne_of_ne (by simp : cv (chainOf j' 0) 13 ≠ gh j)),
              Function.update_of_ne (fin_ne_of_ne (by simp : cv (chainOf j' 1) 13 ≠ gh j)),
              Function.update_of_ne (fin_ne_of_ne (by simp : cv (chainOf j' 2) 13 ≠ gh j))]
            exact t
          · have hnot' : gh j' ∉ gh j :: rest := by
              simp only [List.mem_cons, not_or]
              exact ⟨fun h => same (Name.gh.inj h), hnot⟩
            rw [Function.update_of_ne neGh]
            exact HoldsG.frame hj15 (by omega) same _ (gh_len_le j') groupFrame
              ((facts j' hj').2 hnot')
  · apply Segment.NodeRefines.ofPure
    · simp [ghSeg, ghCode, hj]
    · simp [ghSeg, ghCost, hj]
    · intro s x cursor rest _ inv r hr
      obtain ⟨ctx, held, facts⟩ := inv
      rw [cursorStep_gh, if_neg hj] at hr
      simp only [support_pure, Set.mem_singleton_iff] at hr
      subst hr
      refine ⟨ctx.drop, ?_, ?_⟩
      · intro k hk
        show Holds s k (Function.update x (gh j).fin 0 (cv k 13).fin)
        rw [Function.update_of_ne (fin_ne_of_ne (by simp : cv k 13 ≠ gh j))]
        exact held k hk
      · intro j' hj'
        dsimp only
        have same : j' ≠ j := fun h => hj (h ▸ hj')
        have neGh : (gh j').fin ≠ (gh j).fin := fin_ne_of_ne (fun h => same (Name.gh.inj h))
        refine ⟨fun hmem => ?_, fun hnot => ?_⟩
        · have t := (facts j' hj').1 (by simp [hmem])
          unfold TaggedG at t ⊢
          rw [Function.update_of_ne (fin_ne_of_ne (by simp : gc j' ≠ gh j)),
            Function.update_of_ne (fin_ne_of_ne (by simp : cv (chainOf j' 0) 13 ≠ gh j)),
            Function.update_of_ne (fin_ne_of_ne (by simp : cv (chainOf j' 1) 13 ≠ gh j)),
            Function.update_of_ne (fin_ne_of_ne (by simp : cv (chainOf j' 2) 13 ≠ gh j))]
          exact t
        · have hnot' : gh j' ∉ gh j :: rest := by
            simp only [List.mem_cons, not_or]
            exact ⟨fun h => same (Name.gh.inj h), hnot⟩
          rw [Function.update_of_ne neGh]
          exact (facts j' hj').2 hnot'
    · intro x cursor
      exact ⟨_, by rw [cursorStep_gh, if_neg hj]⟩

/-! ## The group value segment -/

def gvCode : Name → Code
  | .gv j => if 12 ≤ j.val ∧ j.val < 15 then readGroup j.val else []
  | _ => []

def gvCost : Name → ℕ
  | .gv j => if 12 ≤ j.val ∧ j.val < 15 then (readGroup j.val).length else 0
  | _ => 0

/-- Hashed groups keep their answer until read; processed groups hold their value. -/
def GvInv (after : List Name) (s : MachineState) (x : graph.Assignment) (cursor : ℕ)
    (rem : List Name) : Prop :=
  TreeCtx index payload pk s cursor (rem ++ after) ∧
  ∀ j : Fin 21, j.val < 15 →
    (gv j ∈ rem → j.val < 12 → HoldsG s j (x (gh j).fin)) ∧ (gv j ∉ rem → HoldsG s j (x (gv j).fin))

def gvSeg (after : List Name) : Segment := ⟨gvCode, gvCost, GvInv index payload pk after⟩

theorem gv_len_le (j : Fin 21) : graph.len (gv j).fin ≤ 256 := by
  rw [graph_len_fin]; norm_num [Name.len]

theorem readGroup_effect (s : MachineState) (j : ℕ) :
    ((readGroup j).foldl execInstrBr s).getReg .x9 = s.getReg .x9 + 16 ∧
    (∀ r, r ≠ .x9 → r ≠ .x26 → r ≠ .x27 →
      ((readGroup j).foldl execInstrBr s).getReg r = s.getReg r) ∧
    ((readGroup j).foldl execInstrBr s).mem =
      ((copy128 .x9 0 .x20 (groupSlot j)).foldl execInstrBr s).mem := by
  have h16 : signExtend12 (16 : BitVec 12) = (16 : Word) := by decide
  simp only [readGroup, List.foldl_append, List.foldl_cons, List.foldl_nil, execInstrBr, h16]
  refine ⟨?_, ?_, rfl⟩
  · simp only [MachineState.getReg_setPC, MachineState.getReg_setReg_eq (by decide : Reg.x9 ≠ .x0),
      copy128_reg _ .x9 .x20 .x9 0 _ (by decide) (by decide)]
  · intro r h9 h26 h27
    simp only [MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ .x9 r _ h9.symm,
      copy128_reg _ .x9 .x20 r 0 _ h26 h27]

theorem readGroup_ready (s : MachineState) (j : ℕ) (hj : j < 15)
    (base : s.getReg .x20 = BitVec.ofNat 64 groupsBase) (cursor : CursorReady s) :
    Riscv.LinearReady s (readGroup j) := by
  refine (copy128_ready s .x9 .x20 0 (groupSlot j) (by decide) (by decide) (by decide)
    ?_ ?_ ?_ ?_).append ?_
  · simpa only [signExtend12_nonnegative 0 (by decide)] using
      cursor_access s cursor 0 (by decide)
  · simpa only [signExtend12_nonnegative 8 (by decide)] using
      cursor_access s cursor 1 (by decide)
  · rw [signExtend12_nonnegative (groupSlot j) (by unfold groupSlot; omega), base]
    simpa only [Nat.mul_zero, Nat.add_zero] using group_access j 0 hj (by decide)
  · rw [signExtend12_nonnegative (groupSlot j + 8) (by unfold groupSlot; omega), base]
    simpa only [Nat.mul_one] using group_access j 1 hj (by decide)
  · exact ⟨rfl, trivial, trivial⟩

/-- The word read for a disclosed group is the specification's decoded value. -/
theorem gv_value (j : Fin 21) (cursor : ℕ) (t : MachineState)
    (held : MemBits t (groupAddr j) (ofBits 128 (payload.drop cursor))) :
    HoldsG t j (ofBits (graph.len (gv j).fin) ((payload.drop cursor).take (graph.len (gv j).fin))) := by
  have length : graph.len (gv j).fin = 128 := graph_len_fin (gv j)
  unfold HoldsG
  rw [length]
  have take : ofBits 128 ((payload.drop cursor).take 128) = ofBits 128 (payload.drop cursor) := by
    simpa only [List.drop_zero] using
      ofBits_drop_take (payload.drop cursor) (cap := 128) (start := 0) (len := 128) (by decide)
  rw [take]
  exact held

theorem gv_refines (after : List Name) (j : Fin 21) :
    (gvSeg index payload pk after).NodeRefines index payload (gv j) := by
  by_cases hj : 12 ≤ j.val ∧ j.val < 15
  · intro s x cursor rest tail K c budget fuel fresh inv located0 bound continuation
    obtain ⟨ctx, facts⟩ := inv
    have code : gvCode (gv j) = readGroup j := by simp [gvCode, hj]
    have cost : gvCost (gv j) = (readGroup j).length := by simp [gvCost, hj]
    change Riscv.CodeAt s s.pc (gvCode (gv j) ++ tail) at located0
    change (gvCode (gv j)).length + budget ≤ fuel at bound
    rw [code] at located0 bound
    change Riscv.Refines fuel s _ (gvCost (gv j) + c)
    rw [cost, cursorStep_gv, if_pos hj, pure_bind]
    have consumed : consumedBits index (gv j) = 128 := by rw [consumedBits_gv, if_pos hj]
    have room : cursor + 128 ≤ 5248 := ctx.room consumed
    have cursorReady : CursorReady s := ctx.atCursor.ready ctx.bounded ctx.aligned
    have ready := readGroup_ready s j hj.2 ctx.regs.groups cursorReady
    obtain ⟨tCursor, tRegs, tMem⟩ := readGroup_effect s j
    set t := (readGroup j).foldl execInstrBr s with ht
    have tPc : t.pc = s.pc + BitVec.ofNat 64 (4 * (readGroup j).length) :=
      Riscv.linear_fold_pc s _ ready
    have tLocated : Riscv.CodeAt t t.pc tail := by
      rw [tPc]; exact located0.append_right.code_eq (Riscv.fold_code s _)
    have hslot : groupSlot j + 8 < 2048 := by unfold groupSlot; omega
    have hslot' : groupSlot j < 2048 := by omega
    have source : MemBits s (s.getReg .x9 + BitVec.ofNat 64 0) (ofBits 128 (payload.drop cursor)) := by
      rw [BitVec.add_zero]
      exact ctx.context.payload_word cursor ctx.atCursor ctx.aligned room
    have moved := copy128_memBits s .x9 .x20 0 (groupSlot j) (by decide) (by decide) (by decide)
      (by decide) hslot (by rw [BitVec.add_zero]; exact (aligned_iff _).mpr cursorReady.2.2)
      (by rw [ctx.regs.groups]; exact groupAddr_aligned j hj.2) (ofBits 128 (payload.drop cursor))
      source
    rw [ctx.regs.groups] at moved
    have value : HoldsG t j (ofBits (graph.len (gv j).fin)
        ((payload.drop cursor).take (graph.len (gv j).fin))) :=
      gv_value payload j cursor t (memBits_of_mem_eq tMem moved)
    have frame : ∀ addr, (∀ i, i < 4 → addr ≠ groupAddr j + BitVec.ofNat 64 (8 * i)) →
        t.getMem addr = s.getMem addr := by
      intro addr outside
      have h : t.getMem addr = ((copy128 .x9 0 .x20 (groupSlot j)).foldl execInstrBr s).getMem addr := by
        simp only [MachineState.getMem, tMem]
      rw [h, copy128_getMem _ _ _ _ _ (by decide) (by decide) (by decide)]
      simp only [signExtend12_nonnegative 0 (by decide), signExtend12_nonnegative (0 + 8) (by decide),
        signExtend12_nonnegative (groupSlot j) hslot', signExtend12_nonnegative (groupSlot j + 8) hslot,
        ctx.regs.groups]
      have o0 : addr ≠ BitVec.ofNat 64 groupsBase + BitVec.ofNat 64 (groupSlot j) := by
        have := outside 0 (by decide)
        rwa [groupAddr_word, Nat.mul_zero, Nat.add_zero] at this
      have o1 : addr ≠ BitVec.ofNat 64 groupsBase + BitVec.ofNat 64 (groupSlot j + 8) := by
        have := outside 1 (by decide)
        rwa [groupAddr_word, Nat.mul_one] at this
      rw [if_neg o1, if_neg o0]
    have lowFrame : FrameInputs s t := by
      intro addr low
      apply frame addr
      intro i hi
      exact group_ne_low addr (by unfold chainsBase at low; unfold groupsBase; omega) j i hj.2 hi
    have frame' : ∀ addr, (∀ i, i < 4 → addr ≠ groupAddr j + BitVec.ofNat 64 (8 * i)) →
        addr.toNat < scratchBase → t.getMem addr = s.getMem addr :=
      fun addr outside _ => frame addr outside
    rw [show fuel = (readGroup j).length + (fuel - (readGroup j).length) by omega]
    apply Riscv.Refines.linear _ located0.append_left ready
    rw [← ht]
    apply continuation t (Function.update x (gv j).fin
      (ofBits (graph.len (gv j).fin) ((payload.drop cursor).take (graph.len (gv j).fin))), cursor + 128)
      (by rw [cursorStep_gv, if_pos hj]; simp) ?_ tLocated (fuel - (readGroup j).length) (by omega)
    refine ⟨ctx.read consumed lowFrame ?_ tCursor, ?_⟩
    · intro r hr
      apply tRegs r <;> rintro rfl <;> simp at hr
    · intro j' hj'
      dsimp only
      by_cases same : j' = j
      · subst same
        refine ⟨fun h => absurd h fresh, fun _ => ?_⟩
        rw [Function.update_self]
        exact value
      · have neGv : (gv j').fin ≠ (gv j).fin := fin_ne_of_ne (fun h => same (Name.gv.inj h))
        have neGh : (gh j').fin ≠ (gv j).fin := fin_ne_of_ne (by simp)
        refine ⟨fun hmem hj12 => ?_, fun hnot => ?_⟩
        · rw [Function.update_of_ne neGh]
          exact HoldsG.frame hj.2 hj' same _ (gh_len_le j') frame'
            ((facts j' hj').1 (by simp [hmem]) hj12)
        · have hnot' : gv j' ∉ gv j :: rest := by
            simp only [List.mem_cons, not_or]
            exact ⟨fun h => same (Name.gv.inj h), hnot⟩
          rw [Function.update_of_ne neGv]
          exact HoldsG.frame hj.2 hj' same _ (gv_len_le j') frame' ((facts j' hj').2 hnot')
  · apply Segment.NodeRefines.ofPure
    · simp [gvSeg, gvCode, hj]
    · simp [gvSeg, gvCost, hj]
    · intro s x cursor rest fresh inv r hr
      obtain ⟨ctx, facts⟩ := inv
      rw [cursorStep_gv, if_neg hj] at hr
      have value : ∃ v, r = (Function.update x (gv j).fin v, cursor) ∧
          (j.val < 12 → v = (Forest.trunc (x (gh j).fin)).cast (graph_len_fin (gv j)).symm) := by
        split_ifs at hr with h
        · simp only [support_pure, Set.mem_singleton_iff] at hr
          exact ⟨_, hr, fun _ => rfl⟩
        · simp only [support_pure, Set.mem_singleton_iff] at hr
          exact ⟨_, hr, fun hj' => absurd hj' h⟩
      obtain ⟨v, rfl, hv⟩ := value
      refine ⟨ctx.drop, ?_⟩
      intro j' hj'
      dsimp only
      by_cases same : j' = j
      · subst same
        refine ⟨fun hmem => absurd hmem fresh, fun _ => ?_⟩
        rw [Function.update_self]
        have hj12 : j'.val < 12 := by omega
        rw [hv hj12]
        unfold HoldsG
        apply (memBits_cast _ _ _ _).mpr
        exact memBits_trunc ((facts j' hj').1 (by simp) hj12)
      · have neGv : (gv j').fin ≠ (gv j).fin := fin_ne_of_ne (fun h => same (Name.gv.inj h))
        have neGh : (gh j').fin ≠ (gv j).fin := fin_ne_of_ne (by simp)
        refine ⟨fun hmem hj12 => ?_, fun hnot => ?_⟩
        · rw [Function.update_of_ne neGh]
          exact (facts j' hj').1 (by simp [hmem]) hj12
        · have hnot' : gv j' ∉ gv j :: rest := by
            simp only [List.mem_cons, not_or]
            exact ⟨fun h => same (Name.gv.inj h), hnot⟩
          rw [Function.update_of_ne neGv]
          exact (facts j' hj').2 hnot'
    · intro x cursor
      rw [cursorStep_gv, if_neg hj]
      split_ifs <;> exact ⟨_, rfl⟩

/-! ## The group phase -/

theorem gcs_code (after : List Name) : gcs.flatMap (gcSeg index payload pk after).code = [] := by
  simp [gcs, gcSeg, List.flatMap_eq_nil_iff]

theorem ghs_code (after : List Name) :
    ghs.flatMap (ghSeg index payload pk after).code = groupHashes := by
  simp only [ghs, ghSeg, List.flatMap_map, groupHashes]
  rfl

theorem gvs_code (after : List Name) :
    gvs.flatMap (gvSeg index payload pk after).code = groupReads := by
  simp only [gvs, gvSeg, List.flatMap_map, groupReads]
  rfl

theorem gcs_cost (after : List Name) : (gcs.map (gcSeg index payload pk after).cost).sum = 0 := by
  apply List.sum_eq_zero
  intro v hv
  obtain ⟨_, _, rfl⟩ := List.mem_map.mp hv
  rfl

theorem ghs_cost (after : List Name) :
    (ghs.map (ghSeg index payload pk after).cost).sum = groupHashes.length := by
  rw [← ghs_code index payload pk after]
  apply cost_eq_length
  intro n hn
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp hn
  simp only [ghSeg, ghCost, ghCode]
  split_ifs <;> rfl

theorem gvs_cost (after : List Name) :
    (gvs.map (gvSeg index payload pk after).cost).sum = groupReads.length := by
  rw [← gvs_code index payload pk after]
  apply cost_eq_length
  intro n hn
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp hn
  simp only [gvSeg, gvCost, gvCode]
  split_ifs <;> rfl

theorem gc_to_gh (after : List Name) (s : MachineState) (x : graph.Assignment) (cursor : ℕ)
    (h : GcInv index payload pk (ghs ++ gvs ++ after) s x cursor []) :
    GhInv index payload pk (gvs ++ after) s x cursor ghs := by
  obtain ⟨ctx, held, tagged⟩ := h
  refine ⟨by simpa only [List.nil_append, List.append_assoc] using ctx, held, ?_⟩
  intro j hj
  refine ⟨fun _ => tagged j hj (by simp), fun hn => ?_⟩
  exact absurd (List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩) hn

theorem gh_to_gv (after : List Name) (s : MachineState) (x : graph.Assignment) (cursor : ℕ)
    (h : GhInv index payload pk (gvs ++ after) s x cursor []) :
    GvInv index payload pk after s x cursor gvs := by
  obtain ⟨ctx, _, facts⟩ := h
  refine ⟨by simpa only [List.nil_append] using ctx, ?_⟩
  intro j _
  have mem : gv j ∈ gvs := List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩
  exact ⟨fun _ hj12 => (facts j hj12).2 (by simp), fun hn => absurd mem hn⟩

/-- The tree phase's registers and the group values, after the group phase. -/
def GroupsDone (s : MachineState) (x : graph.Assignment) (cursor : ℕ) : Prop :=
  TreeCtx index payload pk s cursor (ecs ++ (ehs ++ (evs ++ [rc, rh]))) ∧
  ∀ j : Fin 21, j.val < 15 → HoldsG s j (x (gv j).fin)

theorem gv_last (s : MachineState) (x : graph.Assignment) (cursor : ℕ)
    (h : GvInv index payload pk (ecs ++ (ehs ++ (evs ++ [rc, rh]))) s x cursor []) :
    GroupsDone index payload pk s x cursor := by
  obtain ⟨ctx, facts⟩ := h
  exact ⟨by simpa only [List.nil_append] using ctx, fun j hj => (facts j hj).2 (by simp)⟩

theorem treeSetup_effect (s : MachineState) :
    (treeSetup.foldl execInstrBr s).getReg .x18 = scratchAddr ∧
    (treeSetup.foldl execInstrBr s).getReg .x19 = BitVec.ofNat 64 chainsBase ∧
    (treeSetup.foldl execInstrBr s).getReg .x20 = BitVec.ofNat 64 groupsBase ∧
    (treeSetup.foldl execInstrBr s).getReg .x21 = BitVec.ofNat 64 subtreesBase ∧
    (treeSetup.foldl execInstrBr s).getReg .x11 = 400 ∧
    (∀ r, r ≠ .x18 → r ≠ .x19 → r ≠ .x20 → r ≠ .x21 → r ≠ .x11 →
      (treeSetup.foldl execInstrBr s).getReg r = s.getReg r) ∧
    (treeSetup.foldl execInstrBr s).mem = s.mem := by
  have l18 : literalValue scratchBase = scratchAddr := by decide +kernel
  have l19 : literalValue chainsBase = BitVec.ofNat 64 chainsBase := by decide +kernel
  have l20 : literalValue groupsBase = BitVec.ofNat 64 groupsBase := by decide +kernel
  have l21 : literalValue subtreesBase = BitVec.ofNat 64 subtreesBase := by decide +kernel
  simp only [treeSetup, List.foldl_append, List.foldl_cons, List.foldl_nil, execInstrBr]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ .x11 .x18 _ (by decide),
      constant_preserves _ .x21 .x18 _ (by decide), constant_preserves _ .x20 .x18 _ (by decide),
      constant_preserves _ .x19 .x18 _ (by decide), constant_value _ .x18 _ (by decide), l18]
  · simp only [MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ .x11 .x19 _ (by decide),
      constant_preserves _ .x21 .x19 _ (by decide), constant_preserves _ .x20 .x19 _ (by decide),
      constant_value _ .x19 _ (by decide), l19]
  · simp only [MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ .x11 .x20 _ (by decide),
      constant_preserves _ .x21 .x20 _ (by decide), constant_value _ .x20 _ (by decide), l20]
  · simp only [MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ .x11 .x21 _ (by decide),
      constant_value _ .x21 _ (by decide), l21]
  · simp only [MachineState.getReg_setPC, MachineState.getReg_setReg_eq (by decide : Reg.x11 ≠ .x0),
      getReg_x0]
    try rfl
  · intro r h18 h19 h20 h21 h11
    simp only [MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ .x11 r _ h11.symm,
      constant_preserves _ .x21 r _ h21.symm, constant_preserves _ .x20 r _ h20.symm,
      constant_preserves _ .x19 r _ h19.symm, constant_preserves _ .x18 r _ h18.symm]
  · simp only [MachineState.setPC, MachineState.setReg, constant_mem]
    try rfl

theorem treeSetup_ready (s : MachineState) : Riscv.LinearReady s treeSetup := by
  refine ((((constant_ready _ _ _).append (constant_ready _ _ _)).append
    (constant_ready _ _ _)).append (constant_ready _ _ _)).append ?_
  exact ⟨rfl, trivial, trivial⟩

theorem treeSetup_length : treeSetup.length = 9 := by decide +kernel

/-- Entering the tree phase from the finished chains establishes the group-input invariant. -/
theorem treeSetup_gcInv (s : MachineState) (x : graph.Assignment) (cursor : ℕ)
    (done : ChainsDone index payload pk s x cursor) :
    GcInv index payload pk (ghs ++ gvs ++ (ecs ++ (ehs ++ (evs ++ [rc, rh]))))
      (treeSetup.foldl execInstrBr s) x cursor gcs := by
  obtain ⟨ctx, held⟩ := done
  obtain ⟨h18, h19, h20, h21, h11, regs, mem⟩ := treeSetup_effect s
  have frame : ∀ addr : Word, (treeSetup.foldl execInstrBr s).getMem addr = s.getMem addr :=
    fun addr => by simp only [MachineState.getMem, mem]
  refine ⟨⟨ctx.context.frameInputs (fun addr _ => frame addr)
    (regs .x8 (by decide) (by decide) (by decide) (by decide) (by decide)),
    ⟨h18, h19, h20, h21, ?_, h11⟩, ?_, ctx.aligned, ?_⟩, ?_, ?_⟩
  · rw [regs .x5 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact ctx.regs.call
  · unfold CursorAt
    rw [regs .x9 (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact ctx.atCursor
  · have := ctx.budget
    rw [treeNodes_split] at this
    simpa only [List.append_assoc] using this
  · intro k hk
    exact memBits_of_mem_eq mem (held k hk)
  · intro j _ hn
    exact absurd (List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩) hn

/-- The whole group phase refines the reader over the group nodes. -/
theorem groups_refines (tail : Code)
    (K : graph.Assignment × ℕ → OracleComp (Spec paperParams) (Option Bool)) (c rest' : ℕ)
    (continuation : ∀ (u : MachineState) (y : graph.Assignment) (cursor' : ℕ),
      GroupsDone index payload pk u y cursor' → Riscv.CodeAt u u.pc tail →
      ∀ left, rest' ≤ left → Riscv.Refines left u (K (y, cursor')) c)
    (s : MachineState) (x : graph.Assignment) (cursor fuel : ℕ)
    (done : ChainsDone index payload pk s x cursor)
    (located : Riscv.CodeAt s s.pc (groups ++ tail)) (bound : groups.length + rest' ≤ fuel) :
    Riscv.Refines fuel s (runNodes' index payload (gcs ++ (ghs ++ gvs)) x cursor >>= K)
      (groups.length + c) := by
  have parts : groups = treeSetup ++ (groupHashes ++ groupReads) := by
    simp only [groups, List.append_assoc]
  rw [parts] at located bound ⊢
  simp only [List.length_append] at bound ⊢
  simp only [List.append_assoc] at located
  set u := treeSetup.foldl execInstrBr s with hu
  have ready := treeSetup_ready s
  have uCode : Riscv.CodeAt u u.pc (groupHashes ++ (groupReads ++ tail)) := by
    rw [hu, Riscv.linear_fold_pc s _ ready]
    exact located.append_right.code_eq (Riscv.fold_code s _)
  have inv := treeSetup_gcInv index payload pk s x cursor done
  simp only [runNodes'_append, bind_assoc]
  rw [show fuel = treeSetup.length + (fuel - treeSetup.length) by
      rw [treeSetup_length] at bound ⊢; omega,
    show treeSetup.length + (groupHashes.length + groupReads.length) + c =
      treeSetup.length + (groupHashes.length + (groupReads.length + c)) by omega]
  apply Riscv.Refines.linear _ located.append_left ready
  rw [← hu]
  have step1 := sweep_refines index payload
    (gcSeg index payload pk (ghs ++ gvs ++ (ecs ++ (ehs ++ (evs ++ [rc, rh]))))) gcs gcs_nodup
    (fun n hn => by
      obtain ⟨j, _, rfl⟩ := List.mem_map.mp hn
      exact gc_refines index payload pk _ j) (groupHashes ++ (groupReads ++ tail))
    (fun r => runNodes' index payload ghs r.1 r.2 >>= fun r' =>
      runNodes' index payload gvs r'.1 r'.2 >>= K)
    (groupHashes.length + (groupReads.length + c)) (groupHashes.length + (groupReads.length + rest'))
    ?_ u x cursor (fuel - treeSetup.length) inv (by rw [gcs_code]; exact uCode)
    (by rw [gcs_code, treeSetup_length] at *; simp only [List.length_nil]; omega)
  · rw [gcs_cost, Nat.zero_add] at step1
    exact step1
  intro v y cursor1 inv1 located1 left hleft
  dsimp only
  have step2 := sweep_refines index payload
    (ghSeg index payload pk (gvs ++ (ecs ++ (ehs ++ (evs ++ [rc, rh]))))) ghs ghs_nodup
    (fun n hn => by
      obtain ⟨j, _, rfl⟩ := List.mem_map.mp hn
      exact gh_refines index payload pk _ j) (groupReads ++ tail)
    (fun r' => runNodes' index payload gvs r'.1 r'.2 >>= K)
    (groupReads.length + c) (groupReads.length + rest') ?_ v y cursor1 left
    (gc_to_gh index payload pk _ v y cursor1 inv1)
    (by rw [ghs_code]; exact located1) (by rw [ghs_code]; omega)
  · rw [ghs_cost] at step2
    exact step2
  intro w z cursor2 inv2 located2 left2 hleft2
  dsimp only
  have step3 := sweep_refines index payload
    (gvSeg index payload pk (ecs ++ (ehs ++ (evs ++ [rc, rh])))) gvs gvs_nodup
    (fun n hn => by
      obtain ⟨j, _, rfl⟩ := List.mem_map.mp hn
      exact gv_refines index payload pk _ j) tail K c rest'
    (fun t y3 cursor3 inv3 located3 left3 hleft3 =>
      continuation t y3 cursor3 (gv_last index payload pk t y3 cursor3 inv3) located3 left3 hleft3)
    w z cursor2 left2 (gh_to_gv index payload pk _ w z cursor2 inv2)
    (by rw [gvs_code]; exact located2) (by rw [gvs_code]; exact hleft2)
  rw [gvs_cost] at step3
  exact step3

end OptimalOTS.RiscvUpperProgram.Compact
