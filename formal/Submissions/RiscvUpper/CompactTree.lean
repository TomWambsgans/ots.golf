import Submissions.RiscvUpper.CompactLevels

/-! The tree phase of the compact image: groups, subtrees, the root hash and the decision. -/

namespace OptimalOTS.RiscvUpperProgram.Compact

open RiscvZkvm.Rv64 Forest Forest.Name RiscvUpperForest.ForestVerifier OracleComp

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
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

variable (index : Fin (2 ^ 115)) (payload : List Bool) (pk : PublicKey paperParams)

structure TreeCtx (s : MachineState) (cursor : ℕ) (rem : List Name) : Prop where
  context : Direct.ExecutionContext s index payload pk
  regs : TreeRegs s
  atCursor : Direct.CursorAt s cursor
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
  · unfold Direct.CursorAt
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
  · unfold Direct.CursorAt
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
  apply Direct.memBits_of_word_frame s t _ v held
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

theorem chainsHeld_frame {s t : MachineState} {x : graph.Assignment}
    (frame : ∀ addr, addr.toNat < groupsBase → t.getMem addr = s.getMem addr)
    (held : ChainsHeld s x) : ChainsHeld t x := fun k hk =>
  holds_of_frame_groups hk _ (cv_len_le k 13) frame (held k hk)


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

theorem consumedBits_gc (j : Fin 21) : consumedBits index (gc j) = 0 := by
  rw [consumedBits_word]; rfl
theorem consumedBits_gh (j : Fin 21) : consumedBits index (gh j) = 0 := by
  rw [consumedBits_word]; rfl

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
    ((Direct.writeTag tag off).foldl execInstrBr s).getMem addr = s.getMem addr := by
  apply Direct.writeTag_frame _ _ _ _ hoff literal
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
  apply Direct.memBits_of_word_frame s t base v held
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
    MemBits ((Direct.writeTag tag off).foldl execInstrBr s) scratchAddr (tag ++ value) := by
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
    Riscv.LinearReady s (Direct.writeTag tag off) := by
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
      (Direct.writeTag (BitVec.ofNat 16 tagN) 48).foldl execInstrBr
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
  have r4 : Riscv.LinearReady s3 (Direct.writeTag (BitVec.ofNat 16 tagN) 48) :=
    tag_scratch_ready s3 _ 48 (by decide) (by decide) x18₃
  have g4 : ∀ r, r ≠ .x26 →
      ((Direct.writeTag (BitVec.ofNat 16 tagN) 48).foldl execInstrBr s3).getReg r = s3.getReg r :=
    fun r h26 => Direct.writeTag_register s3 _ _ r h26
  have f4 : ∀ addr : Word, addr.toNat < scratchBase →
      ((Direct.writeTag (BitVec.ofNat 16 tagN) 48).foldl execInstrBr s3).getMem addr = s3.getMem addr :=
    fun addr low' => tag_scratch_frame s3 _ 48 (by decide) literal x18₃ addr low'
  have m4 : MemBits ((Direct.writeTag (BitVec.ofNat 16 tagN) 48).foldl execInstrBr s3) scratchAddr
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

theorem chainOf_val0 (j : Fin 21) : (chainOf j 0).val = 3 * j.val := rfl
theorem chainOf_val1 (j : Fin 21) : (chainOf j 0).val = 3 * j.val := rfl

theorem gc_len (j : Fin 21) : graph.len (gc j).fin = 400 := graph_len_fin (gc j)
theorem gh_len_le (j : Fin 21) : graph.len (gh j).fin ≤ 256 := by
  rw [graph_len_fin]; norm_num [Name.len]

theorem groupTag_literal (j : Fin 21) :
    (literalValue (BitVec.ofNat 16 (2730 + j.val)).toNat).truncate 16 = BitVec.ofNat 16 (2730 + j.val) :=
  Direct.nodeTag_literal (.gh j)

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
      apply (Direct.memBits_cast _ _ _ _).mpr
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
  apply Direct.memBits_of_word_frame s t _ v held
  intro i hi
  rw [aligned_bit_word _ ((aligned_iff _).mp (groupAddr_aligned j' hj')) i
    (by rw [groupAddr_toNat j' hj']; unfold groupsBase groupSlot; omega)]
  apply frame
  · intro i' hi'
    exact groupAddr_word_ne j' j hj' hj (i / 64) i' (by omega) hi' (fun h => different (Fin.ext h))
  · exact groupAddr_low j' hj' (i / 64) (by omega)

/-- Group slots survive writes into the scratch buffer and above. -/
theorem HoldsG.frameScratch {s t : MachineState} {j : Fin 21} (hj : j.val < 15) {w : ℕ} (v : BitVec w)
    (small : w ≤ 256)
    (frame : ∀ addr : Word, addr.toNat < scratchBase → t.getMem addr = s.getMem addr)
    (held : HoldsG s j v) : HoldsG t j v := by
  apply memBits_frame_low _ frame held
  rw [groupAddr_toNat j hj]
  unfold groupsBase groupSlot scratchBase
  omega

/-- The value of a node truncates to its first machine word. -/
theorem memBits_trunc {s : MachineState} {base : Word} {n : Name} {x : graph.Assignment}
    (held : MemBits s base (x n.fin)) : MemBits s base (Forest.trunc (x n.fin)) := by
  have bound : 0 + 128 ≤ graph.len n.fin := by
    rw [graph_len_fin]
    exact Direct.node_length_positive n
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
      apply (Direct.memBits_cast _ _ _ _).mpr
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
    (base : s.getReg .x20 = BitVec.ofNat 64 groupsBase) (cursor : Direct.CursorReady s) :
    Riscv.LinearReady s (readGroup j) := by
  refine (copy128_ready s .x9 .x20 0 (groupSlot j) (by decide) (by decide) (by decide)
    ?_ ?_ ?_ ?_).append ?_
  · simpa only [signExtend12_nonnegative 0 (by decide)] using
      Direct.cursor_access s cursor 0 (by decide)
  · simpa only [signExtend12_nonnegative 8 (by decide)] using
      Direct.cursor_access s cursor 1 (by decide)
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
    have cursorReady : Direct.CursorReady s := ctx.atCursor.ready ctx.bounded ctx.aligned
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
        apply (Direct.memBits_cast _ _ _ _).mpr
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
  · unfold Direct.CursorAt
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

theorem consumedBits_ec (l : Fin 7) : consumedBits index (ec l) = 0 := by
  rw [consumedBits_word]; rfl
theorem consumedBits_eh (l : Fin 7) : consumedBits index (eh l) = 0 := by
  rw [consumedBits_word]; rfl
theorem consumedBits_rc : consumedBits index rc = 0 := by
  rw [consumedBits_word]; rfl
theorem consumedBits_rh : consumedBits index rh = 0 := by
  rw [consumedBits_word]; rfl

theorem ec_len (l : Fin 7) : graph.len (ec l).fin = 400 := graph_len_fin (ec l)
theorem eh_len_le (l : Fin 7) : graph.len (eh l).fin ≤ 256 := by
  rw [graph_len_fin]; norm_num [Name.len]
theorem ev_len_le (l : Fin 7) : graph.len (ev l).fin ≤ 256 := by
  rw [graph_len_fin]; norm_num [Name.len]

theorem subtreeTag_literal (l : Fin 7) :
    (literalValue (BitVec.ofNat 16 (2779 + l.val)).toNat).truncate 16 = BitVec.ofNat 16 (2779 + l.val) :=
  Direct.nodeTag_literal (.eh l)

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
  apply Direct.memBits_of_word_frame s t _ v held
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
  apply Direct.memBits_of_word_frame s t _ v held
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

theorem groupsHeld_frame {s t : MachineState} {x : graph.Assignment}
    (frame : ∀ addr : Word, addr.toNat < subtreesBase → t.getMem addr = s.getMem addr)
    (held : GroupsHeld s x) : GroupsHeld t x := fun j hj =>
  holdsG_of_frame_subtrees hj _ (gv_len_le j) frame (held j hj)

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
      apply (Direct.memBits_cast _ _ _ _).mpr
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
      apply (Direct.memBits_cast _ _ _ _).mpr
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
    (base : s.getReg .x21 = BitVec.ofNat 64 subtreesBase) (cursor : Direct.CursorReady s) :
    Riscv.LinearReady s (readSubtree l) := by
  refine (copy128_ready s .x9 .x21 0 (subtreeSlot l) (by decide) (by decide) (by decide)
    ?_ ?_ ?_ ?_).append ?_
  · simpa only [signExtend12_nonnegative 0 (by decide)] using
      Direct.cursor_access s cursor 0 (by decide)
  · simpa only [signExtend12_nonnegative 8 (by decide)] using
      Direct.cursor_access s cursor 1 (by decide)
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
    have cursorReady : Direct.CursorReady s := ctx.atCursor.ready ctx.bounded ctx.aligned
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
        apply (Direct.memBits_cast _ _ _ _).mpr
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

/-! ## The root -/

theorem cursorStep_rc (x : graph.Assignment) (cursor : ℕ) :
    cursorStep index payload x cursor rc =
      pure (Function.update x rc.fin
        ((tw rh ++ cat7 fun l => Forest.trunc (x (ev l).fin)).cast (graph_len_fin rc).symm), cursor) := by
  unfold cursorStep
  rw [if_neg (by simp [disclosed]), if_pos (by simp [evaluated]), runOp_eq]
  simp only [evalName, map_pure, detVal_rc]

theorem cursorStep_rh (x : graph.Assignment) (cursor : ℕ) :
    cursorStep index payload x cursor rh =
      (fun y => (Function.update x rh.fin (y.cast (graph_len_fin rh).symm), cursor)) <$>
        hash paperParams (x rc.fin) := by
  unfold cursorStep
  rw [if_neg (by simp [disclosed]), if_pos (by simp [evaluated]), runOp_eq]
  simp only [evalName, Functor.map_map]

theorem rc_len : graph.len rc.fin = 912 := graph_len_fin rc

theorem rootTag_literal :
    (literalValue (BitVec.ofNat 16 2794).toNat).truncate 16 = BitVec.ofNat 16 2794 :=
  Direct.nodeTag_literal .rh

theorem cat7_assoc (v : Fin 7 → BitVec 128) :
    cat7 v = v 0 ++ (v 1 ++ (v 2 ++ (v 3 ++ (v 4 ++ (v 5 ++ v 6))))) := by
  simp only [cat7, BitVec.append_assoc, BitVec.cast_eq]

/-- The linear part of the root block. -/
def rootLin : Code :=
  copy128 .x21 (subtreeSlot 6) .x18 0 ++ copy128 .x21 (subtreeSlot 5) .x18 16 ++
  copy128 .x21 (subtreeSlot 4) .x18 32 ++ copy128 .x21 (subtreeSlot 3) .x18 48 ++
  copy128 .x21 (subtreeSlot 2) .x18 64 ++ copy128 .x21 (subtreeSlot 1) .x18 80 ++
  copy128 .x21 (subtreeSlot 0) .x18 96 ++ Direct.writeTag (BitVec.ofNat 16 2794) 112 ++
  [.ADDI .x10 .x18 0, .ADDI .x11 .x0 912, .ADDI .x12 .x18 128]

theorem root_parts : root = rootLin ++ [Instr.ECALL] := by decide +kernel
theorem root_length : root.length = rootLin.length + 1 := by rw [root_parts]; simp
theorem rootLin_length : rootLin.length = 34 := by decide +kernel

/-- One copy of a subtree word into the scratch buffer, appended after a packed prefix. -/
theorem subtree_step {width : ℕ} (s : MachineState) (l : ℕ) (hl : l < 7) (off : ℕ) (lo : BitVec width)
    (hi : BitVec 128) (bounded : width ≤ 896) (wordAligned : width % 64 = 0)
    (hoff : off = width / 8) (x18 : s.getReg .x18 = scratchAddr)
    (x21 : s.getReg .x21 = BitVec.ofNat 64 subtreesBase)
    (preceding : MemBits s scratchAddr lo) (source : HoldsE s ⟨l, hl⟩ hi) :
    Riscv.LinearReady s (copy128 .x21 (subtreeSlot l) .x18 off) ∧
    (∀ r, r ≠ .x26 → r ≠ .x27 →
      ((copy128 .x21 (subtreeSlot l) .x18 off).foldl execInstrBr s).getReg r = s.getReg r) ∧
    (∀ addr : Word, addr.toNat < scratchBase →
      ((copy128 .x21 (subtreeSlot l) .x18 off).foldl execInstrBr s).getMem addr = s.getMem addr) ∧
    MemBits ((copy128 .x21 (subtreeSlot l) .x18 off).foldl execInstrBr s) scratchAddr (hi ++ lo) := by
  have hslot : subtreeSlot l + 8 < 2048 := by unfold subtreeSlot; omega
  have hoff' : off + 8 < 2048 := by omega
  have hoff8 : off % 8 = 0 := by omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply copy128_ready s .x21 .x18 (subtreeSlot l) off (by decide) (by decide) (by decide)
    · rw [signExtend12_nonnegative (subtreeSlot l) (by omega), x21]
      simpa only [Nat.mul_zero, Nat.add_zero] using subtree_access l 0 hl (by decide)
    · rw [signExtend12_nonnegative (subtreeSlot l + 8) hslot, x21]
      simpa only [Nat.mul_one] using subtree_access l 1 hl (by decide)
    · rw [signExtend12_nonnegative off (by omega), x18]
      exact scratch_word_access off (by omega) hoff8
    · rw [signExtend12_nonnegative (off + 8) hoff', x18]
      exact scratch_word_access (off + 8) (by omega) (by omega)
  · intro r h26 h27
    exact copy128_reg s .x21 .x18 r _ _ h26 h27
  · intro addr low
    exact copy_scratch_frame s .x21 (subtreeSlot l) off (by decide) hoff' x18 addr low
  · apply scratch_append s .x21 (subtreeSlot l) off lo hi bounded wordAligned hoff (by decide) hslot x18
    · rw [x21]; exact subtreeAddr_aligned l hl
    · exact preceding
    · rw [x21]; exact source

/-- The first copy of the root input: subtree 6 at offset 0. -/
theorem subtree_first (s : MachineState) (hi : BitVec 128) (x18 : s.getReg .x18 = scratchAddr)
    (x21 : s.getReg .x21 = BitVec.ofNat 64 subtreesBase) (source : HoldsE s 6 hi) :
    Riscv.LinearReady s (copy128 .x21 (subtreeSlot 6) .x18 0) ∧
    (∀ r, r ≠ .x26 → r ≠ .x27 →
      ((copy128 .x21 (subtreeSlot 6) .x18 0).foldl execInstrBr s).getReg r = s.getReg r) ∧
    (∀ addr : Word, addr.toNat < scratchBase →
      ((copy128 .x21 (subtreeSlot 6) .x18 0).foldl execInstrBr s).getMem addr = s.getMem addr) ∧
    MemBits ((copy128 .x21 (subtreeSlot 6) .x18 0).foldl execInstrBr s) scratchAddr hi := by
  have hslot : subtreeSlot 6 + 8 < 2048 := by decide
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply copy128_ready s .x21 .x18 (subtreeSlot 6) 0 (by decide) (by decide) (by decide)
    · rw [signExtend12_nonnegative (subtreeSlot 6) (by decide), x21]
      simpa only [Nat.mul_zero, Nat.add_zero] using subtree_access 6 0 (by decide) (by decide)
    · rw [signExtend12_nonnegative (subtreeSlot 6 + 8) hslot, x21]
      simpa only [Nat.mul_one] using subtree_access 6 1 (by decide) (by decide)
    · rw [signExtend12_nonnegative 0 (by decide), x18]
      exact scratch_word_access 0 (by decide) (by decide)
    · rw [signExtend12_nonnegative (0 + 8) (by decide), x18]
      exact scratch_word_access (0 + 8) (by decide) (by decide)
  · intro r h26 h27
    exact copy128_reg s .x21 .x18 r _ _ h26 h27
  · intro addr low
    exact copy_scratch_frame s .x21 (subtreeSlot 6) 0 (by decide) (by decide) x18 addr low
  · have h := copy128_memBits s .x21 .x18 (subtreeSlot 6) 0 (by decide) (by decide) (by decide)
      hslot (by decide) (by rw [x21]; exact subtreeAddr_aligned 6 (by decide))
      (by rw [x18, BitVec.add_zero]; exact (aligned_iff _).mpr scratchAddr_aligned) hi
      (by rw [x21]; exact source)
    rw [x18, BitVec.add_zero] at h
    exact h

/-- The values of the subtrees, as a function. -/
def subtreeVals (x : graph.Assignment) : Fin 7 → BitVec 128 := fun l => Forest.trunc (x (ev l).fin)

/-- The root block's linear part packs the 912-bit root input and sets up the hash call. -/
theorem rootLin_effect (s : MachineState) (regs : TreeRegs s) (x : graph.Assignment)
    (held : ∀ l : Fin 7, HoldsE s l (x (ev l).fin))
    (tagged : x rc.fin = (tw rh ++ cat7 fun l => Forest.trunc (x (ev l).fin)).cast (graph_len_fin rc).symm) :
    Riscv.LinearReady s rootLin ∧
    (rootLin.foldl execInstrBr s).getReg .x10 = scratchAddr ∧
    (rootLin.foldl execInstrBr s).getReg .x11 = 912 ∧
    (rootLin.foldl execInstrBr s).getReg .x12 = scratchAddr + BitVec.ofNat 64 128 ∧
    (∀ r, r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → r ≠ .x26 → r ≠ .x27 →
      (rootLin.foldl execInstrBr s).getReg r = s.getReg r) ∧
    (∀ addr : Word, addr.toNat < scratchBase →
      (rootLin.foldl execInstrBr s).getMem addr = s.getMem addr) ∧
    MemBits (rootLin.foldl execInstrBr s) scratchAddr (x rc.fin) := by
  have trunced : ∀ l : Fin 7, HoldsE s l (subtreeVals x l) := fun l => memBits_trunc (held l)
  set v := subtreeVals x with hv
  have unfolded : rootLin.foldl execInstrBr s =
      [Instr.ADDI .x10 .x18 0, .ADDI .x11 .x0 912, .ADDI .x12 .x18 128].foldl execInstrBr
        ((Direct.writeTag (BitVec.ofNat 16 2794) 112).foldl execInstrBr
          ((copy128 .x21 (subtreeSlot 0) .x18 96).foldl execInstrBr
            ((copy128 .x21 (subtreeSlot 1) .x18 80).foldl execInstrBr
              ((copy128 .x21 (subtreeSlot 2) .x18 64).foldl execInstrBr
                ((copy128 .x21 (subtreeSlot 3) .x18 48).foldl execInstrBr
                  ((copy128 .x21 (subtreeSlot 4) .x18 32).foldl execInstrBr
                    ((copy128 .x21 (subtreeSlot 5) .x18 16).foldl execInstrBr
                      ((copy128 .x21 (subtreeSlot 6) .x18 0).foldl execInstrBr s)))))))) := by
    simp only [rootLin, List.foldl_append]
  -- the seven copies
  obtain ⟨r1, g1, f1, m1⟩ := subtree_first s (v 6) regs.scratch regs.subtrees (trunced 6)
  set s1 := (copy128 .x21 (subtreeSlot 6) .x18 0).foldl execInstrBr s with hs1
  have x18₁ : s1.getReg .x18 = scratchAddr := by rw [g1 .x18 (by decide) (by decide), regs.scratch]
  have x21₁ : s1.getReg .x21 = BitVec.ofNat 64 subtreesBase := by
    rw [g1 .x21 (by decide) (by decide), regs.subtrees]
  have e1 : ∀ l, HoldsE s1 l (v l) := fun l =>
    HoldsE.frameScratch (v l) (by decide) f1 (trunced l)
  obtain ⟨r2, g2, f2, m2⟩ := subtree_step s1 5 (by decide) 16 (v 6) (v 5) (by decide) (by decide) rfl x18₁ x21₁ m1 (e1 5)
  set s2 := (copy128 .x21 (subtreeSlot 5) .x18 16).foldl execInstrBr s1 with hs2
  have x18₂ : s2.getReg .x18 = scratchAddr := by rw [g2 .x18 (by decide) (by decide), x18₁]
  have x21₂ : s2.getReg .x21 = BitVec.ofNat 64 subtreesBase := by rw [g2 .x21 (by decide) (by decide), x21₁]
  have e2 : ∀ l, HoldsE s2 l (v l) := fun l => HoldsE.frameScratch (v l) (by decide) f2 (e1 l)
  obtain ⟨r3, g3, f3, m3⟩ := subtree_step s2 4 (by decide) 32 (v 5 ++ v 6) (v 4) (by decide) (by decide) rfl x18₂ x21₂ m2 (e2 4)
  set s3 := (copy128 .x21 (subtreeSlot 4) .x18 32).foldl execInstrBr s2 with hs3
  have x18₃ : s3.getReg .x18 = scratchAddr := by rw [g3 .x18 (by decide) (by decide), x18₂]
  have x21₃ : s3.getReg .x21 = BitVec.ofNat 64 subtreesBase := by rw [g3 .x21 (by decide) (by decide), x21₂]
  have e3 : ∀ l, HoldsE s3 l (v l) := fun l => HoldsE.frameScratch (v l) (by decide) f3 (e2 l)
  obtain ⟨r4, g4, f4, m4⟩ := subtree_step s3 3 (by decide) 48 (v 4 ++ (v 5 ++ v 6)) (v 3) (by decide) (by decide) rfl x18₃ x21₃ m3 (e3 3)
  set s4 := (copy128 .x21 (subtreeSlot 3) .x18 48).foldl execInstrBr s3 with hs4
  have x18₄ : s4.getReg .x18 = scratchAddr := by rw [g4 .x18 (by decide) (by decide), x18₃]
  have x21₄ : s4.getReg .x21 = BitVec.ofNat 64 subtreesBase := by rw [g4 .x21 (by decide) (by decide), x21₃]
  have e4 : ∀ l, HoldsE s4 l (v l) := fun l => HoldsE.frameScratch (v l) (by decide) f4 (e3 l)
  obtain ⟨r5, g5, f5, m5⟩ := subtree_step s4 2 (by decide) 64 (v 3 ++ (v 4 ++ (v 5 ++ v 6))) (v 2) (by decide) (by decide) rfl x18₄ x21₄ m4 (e4 2)
  set s5 := (copy128 .x21 (subtreeSlot 2) .x18 64).foldl execInstrBr s4 with hs5
  have x18₅ : s5.getReg .x18 = scratchAddr := by rw [g5 .x18 (by decide) (by decide), x18₄]
  have x21₅ : s5.getReg .x21 = BitVec.ofNat 64 subtreesBase := by rw [g5 .x21 (by decide) (by decide), x21₄]
  have e5 : ∀ l, HoldsE s5 l (v l) := fun l => HoldsE.frameScratch (v l) (by decide) f5 (e4 l)
  obtain ⟨r6, g6, f6, m6⟩ := subtree_step s5 1 (by decide) 80 (v 2 ++ (v 3 ++ (v 4 ++ (v 5 ++ v 6)))) (v 1) (by decide) (by decide) rfl x18₅ x21₅ m5 (e5 1)
  set s6 := (copy128 .x21 (subtreeSlot 1) .x18 80).foldl execInstrBr s5 with hs6
  have x18₆ : s6.getReg .x18 = scratchAddr := by rw [g6 .x18 (by decide) (by decide), x18₅]
  have x21₆ : s6.getReg .x21 = BitVec.ofNat 64 subtreesBase := by rw [g6 .x21 (by decide) (by decide), x21₅]
  have e6 : ∀ l, HoldsE s6 l (v l) := fun l => HoldsE.frameScratch (v l) (by decide) f6 (e5 l)
  obtain ⟨r7, g7, f7, m7⟩ := subtree_step s6 0 (by decide) 96 (v 1 ++ (v 2 ++ (v 3 ++ (v 4 ++ (v 5 ++ v 6))))) (v 0) (by decide) (by decide) rfl x18₆ x21₆ m6 (e6 0)
  set s7 := (copy128 .x21 (subtreeSlot 0) .x18 96).foldl execInstrBr s6 with hs7
  have x18₇ : s7.getReg .x18 = scratchAddr := by rw [g7 .x18 (by decide) (by decide), x18₆]
  -- the tag
  have r8 : Riscv.LinearReady s7 (Direct.writeTag (BitVec.ofNat 16 2794) 112) :=
    tag_scratch_ready s7 _ 112 (by decide) (by decide) x18₇
  set s8 := (Direct.writeTag (BitVec.ofNat 16 2794) 112).foldl execInstrBr s7 with hs8
  have g8 : ∀ r, r ≠ .x26 → s8.getReg r = s7.getReg r := fun r h26 =>
    Direct.writeTag_register s7 _ _ r h26
  have f8 : ∀ addr : Word, addr.toNat < scratchBase → s8.getMem addr = s7.getMem addr :=
    fun addr low => tag_scratch_frame s7 _ 112 (by decide) rootTag_literal x18₇ addr low
  have m8 : MemBits s8 scratchAddr (BitVec.ofNat 16 2794 ++
      (v 0 ++ (v 1 ++ (v 2 ++ (v 3 ++ (v 4 ++ (v 5 ++ v 6))))))) :=
    scratch_tag s7 112 _ _ (by decide) (by decide) rfl rootTag_literal x18₇ m7
  have x18₈ : s8.getReg .x18 = scratchAddr := by rw [g8 .x18 (by decide), x18₇]
  -- registers and memory through the copies and the tag
  have gAll : ∀ r, r ≠ .x26 → r ≠ .x27 → s8.getReg r = s.getReg r := by
    intro r h26 h27
    rw [g8 r h26, g7 r h26 h27, g6 r h26 h27, g5 r h26 h27, g4 r h26 h27, g3 r h26 h27,
      g2 r h26 h27, g1 r h26 h27]
  have fAll : ∀ addr : Word, addr.toNat < scratchBase → s8.getMem addr = s.getMem addr := by
    intro addr low
    rw [f8 addr low, f7 addr low, f6 addr low, f5 addr low, f4 addr low, f3 addr low, f2 addr low,
      f1 addr low]
  have zero : signExtend12 (0 : BitVec 12) = 0#64 := by decide
  have l912 : signExtend12 (912 : BitVec 12) = (912 : Word) := by decide
  have l128 : signExtend12 (128 : BitVec 12) = BitVec.ofNat 64 128 := by decide
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold rootLin
    refine Riscv.LinearReady.append ?_ ⟨rfl, trivial, rfl, trivial, rfl, trivial, trivial⟩
    refine Riscv.LinearReady.append ?_ (by simpa only [List.foldl_append] using r8)
    refine Riscv.LinearReady.append ?_ (by simpa only [List.foldl_append] using r7)
    refine Riscv.LinearReady.append ?_ (by simpa only [List.foldl_append] using r6)
    refine Riscv.LinearReady.append ?_ (by simpa only [List.foldl_append] using r5)
    refine Riscv.LinearReady.append ?_ (by simpa only [List.foldl_append] using r4)
    refine Riscv.LinearReady.append ?_ (by simpa only [List.foldl_append] using r3)
    exact Riscv.LinearReady.append r1 r2
  · rw [unfolded]
    simp only [List.foldl_cons, List.foldl_nil, execInstrBr, zero, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ .x12 .x10 _ (by decide),
      MachineState.getReg_setReg_ne _ .x11 .x10 _ (by decide),
      MachineState.getReg_setReg_eq (by decide : Reg.x10 ≠ .x0)]
    rw [x18₈, BitVec.add_zero]
  · rw [unfolded]
    simp only [List.foldl_cons, List.foldl_nil, execInstrBr, l912, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ .x12 .x11 _ (by decide),
      MachineState.getReg_setReg_eq (by decide : Reg.x11 ≠ .x0), getReg_x0]
    try rfl
  · rw [unfolded]
    simp only [List.foldl_cons, List.foldl_nil, execInstrBr, l128, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x12 ≠ .x0),
      MachineState.getReg_setReg_ne _ .x11 .x18 _ (by decide),
      MachineState.getReg_setReg_ne _ .x10 .x18 _ (by decide)]
    rw [x18₈]
  · intro r h10 h11 h12 h26 h27
    rw [unfolded]
    simp only [List.foldl_cons, List.foldl_nil, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ .x12 r _ h12.symm,
      MachineState.getReg_setReg_ne _ .x11 r _ h11.symm,
      MachineState.getReg_setReg_ne _ .x10 r _ h10.symm]
    exact gAll r h26 h27
  · intro addr low
    rw [unfolded]
    simp only [List.foldl_cons, List.foldl_nil, execInstrBr, MachineState.getMem_setPC,
      MachineState.getMem_setReg]
    exact fAll addr low
  · rw [unfolded]
    simp only [List.foldl_cons, List.foldl_nil, execInstrBr]
    have value : MemBits s8 scratchAddr (x rc.fin) := by
      rw [tagged]
      apply (Direct.memBits_cast _ _ _ _).mpr
      rw [cat7_assoc]
      exact m8
    exact memBits_of_mem_eq rfl value

/-! ## The decision -/

def decisionPrefix : Code :=
  constant .x7 Riscv.publicKeyBase.toNat ++
  [.LD .x26 .x18 128, .LD .x27 .x7 0, .XOR .x26 .x26 .x27,
   .LD .x24 .x18 136, .LD .x25 .x7 8, .XOR .x24 .x24 .x25,
   .OR .x10 .x26 .x24, .SLTIU .x10 .x10 1, .ADDI .x5 .x0 0]

theorem decision_parts : decision = decisionPrefix ++ [Instr.ECALL] := by decide +kernel
theorem decisionPrefix_length : decisionPrefix.length = 11 := by decide +kernel
theorem decision_length : decision.length = 12 := by decide +kernel

theorem publicKey_literal : literalValue Riscv.publicKeyBase.toNat = Riscv.publicKeyBase := by
  decide +kernel

theorem publicKey_access0 : isValidDwordAccess Riscv.publicKeyBase = true := by decide +kernel
theorem publicKey_access8 : isValidDwordAccess (Riscv.publicKeyBase + 8) = true := by decide +kernel
theorem publicKey_aligned0 : alignToDword Riscv.publicKeyBase = Riscv.publicKeyBase := by decide +kernel
theorem publicKey_aligned8 : alignToDword (Riscv.publicKeyBase + 8) = Riscv.publicKeyBase + 8 := by
  decide +kernel
theorem publicKey_toNat : Riscv.publicKeyBase.toNat = 4194304 := by decide
theorem scratchAddr_toNat : scratchAddr.toNat = 6307840 := by decide

theorem rootAddr_access : isValidDwordAccess (scratchAddr + BitVec.ofNat 64 128) = true :=
  scratch_word_access 128 (by decide) (by decide)
theorem rootAddr_access8 : isValidDwordAccess (scratchAddr + BitVec.ofNat 64 136) = true :=
  scratch_word_access 136 (by decide) (by decide)
theorem rootAddr_aligned :
    alignToDword (scratchAddr + BitVec.ofNat 64 128) = scratchAddr + BitVec.ofNat 64 128 :=
  aligned_offset _ scratchAddr_aligned 128 (by decide) (by decide)
theorem rootAddr_aligned8 :
    alignToDword (scratchAddr + BitVec.ofNat 64 128 + 8) = scratchAddr + BitVec.ofNat 64 128 + 8 := by
  decide +kernel
theorem addr136 : scratchAddr + BitVec.ofNat 64 136 = scratchAddr + BitVec.ofNat 64 128 + 8 := by
  decide +kernel

theorem decisionPrefix_ready (s : MachineState) (x18 : s.getReg .x18 = scratchAddr) :
    Riscv.LinearReady s decisionPrefix := by
  have l128 : signExtend12 (128 : BitVec 12) = BitVec.ofNat 64 128 := by decide
  have l136 : signExtend12 (136 : BitVec 12) = BitVec.ofNat 64 136 := by decide
  have l0 : signExtend12 (0 : BitVec 12) = 0#64 := by decide
  have l8 : signExtend12 (8 : BitVec 12) = (8 : Word) := by decide
  unfold decisionPrefix
  apply (constant_ready _ _ _).append
  have x7 : ((constant .x7 Riscv.publicKeyBase.toNat).foldl execInstrBr s).getReg .x7 =
      Riscv.publicKeyBase := by
    rw [constant_value _ _ _ (by decide), publicKey_literal]
  have x18' : ((constant .x7 Riscv.publicKeyBase.toNat).foldl execInstrBr s).getReg .x18 = scratchAddr := by
    rw [constant_preserves _ _ _ _ (by decide), x18]
  generalize (constant .x7 Riscv.publicKeyBase.toNat).foldl execInstrBr s = u at x7 x18'
  simp only [Riscv.LinearReady, Riscv.linearInstruction, Riscv.memoryReady, execInstrBr,
    MachineState.getReg_setPC, MachineState.getReg_setReg_ne, MachineState.getReg_setReg_eq,
    l128, l136, l0, l8, true_and, and_true, x7, x18', BitVec.add_zero, ne_eq, reduceCtorEq,
    not_false_eq_true]
  exact ⟨rootAddr_access, publicKey_access0, rootAddr_access8, publicKey_access8⟩

private theorem words_equal (a b c d : Word) :
    (if ((a ^^^ b) ||| (c ^^^ d)).ult 1 then (1 : Word) else 0) =
      BitVec.ofNat 64 (decide (a = b ∧ c = d)).toNat := by
  have hz (w : Word) : w.toNat = 0 ↔ w = 0 := by
    constructor
    · intro h
      exact BitVec.eq_of_toNat_eq h
    · rintro rfl
      rfl
  simp only [BitVec.ult]
  by_cases h : a = b ∧ c = d <;> simp [h]
  intro hab hcd
  exact h ⟨BitVec.eq_of_toNat_eq hab, BitVec.eq_of_toNat_eq hcd⟩

private theorem split128_equal (a b : BitVec 128) :
    a.extractLsb' 0 64 = b.extractLsb' 0 64 ∧
      a.extractLsb' 64 64 = b.extractLsb' 64 64 ↔ a = b := by
  constructor
  · rintro ⟨lo, hi⟩
    calc
      a = a.extractLsb' 64 64 ++ a.extractLsb' 0 64 :=
        (BitVec.extractLsb'_append_extractLsb' (w := 64) (len := 64) (x := a)).symm
      _ = b.extractLsb' 64 64 ++ b.extractLsb' 0 64 := by rw [lo, hi]
      _ = b := BitVec.extractLsb'_append_extractLsb' (w := 64) (len := 64) (x := b)
  · rintro rfl
    exact ⟨rfl, rfl⟩

private theorem high_word {s : MachineState} {base : Word} {v : BitVec 128}
    (aligned : alignToDword (base + 8) = base + 8) (memory : MemBits s base v) :
    s.getMem (base + 8) = v.extractLsb' 64 64 := by
  have hm := memBits_extract (start := 64) (len := 64) memory (by decide) (by decide)
  have hw := getMem_of_memBits (by decide : 64 ≤ 64) aligned hm
  simpa using hw

/-- The decision prefix computes the 128-bit comparison and clears the call register. -/
theorem decisionPrefix_effect (s : MachineState) (root key : BitVec 128)
    (x18 : s.getReg .x18 = scratchAddr)
    (hroot : MemBits s (scratchAddr + BitVec.ofNat 64 128) root)
    (hpk : MemBits s Riscv.publicKeyBase key) :
    (decisionPrefix.foldl execInstrBr s).getReg .x10 = BitVec.ofNat 64 (decide (root = key)).toNat ∧
    (decisionPrefix.foldl execInstrBr s).getReg .x5 = 0 := by
  have l128 : signExtend12 (128 : BitVec 12) = BitVec.ofNat 64 128 := by decide
  have l136 : signExtend12 (136 : BitVec 12) = BitVec.ofNat 64 136 := by decide
  have l0 : signExtend12 (0 : BitVec 12) = 0#64 := by decide
  have l8 : signExtend12 (8 : BitVec 12) = (8 : Word) := by decide
  have l1 : signExtend12 (1 : BitVec 12) = (1 : Word) := by decide
  have x7 : ((constant .x7 Riscv.publicKeyBase.toNat).foldl execInstrBr s).getReg .x7 =
      Riscv.publicKeyBase := by
    rw [constant_value _ _ _ (by decide), publicKey_literal]
  have x18' : ((constant .x7 Riscv.publicKeyBase.toNat).foldl execInstrBr s).getReg .x18 = scratchAddr := by
    rw [constant_preserves _ _ _ _ (by decide), x18]
  have mem' : ((constant .x7 Riscv.publicKeyBase.toNat).foldl execInstrBr s).mem = s.mem :=
    constant_mem _ _ _
  have hroot' : MemBits ((constant .x7 Riscv.publicKeyBase.toNat).foldl execInstrBr s)
      (scratchAddr + BitVec.ofNat 64 128) root := memBits_of_mem_eq mem' hroot
  have hpk' : MemBits ((constant .x7 Riscv.publicKeyBase.toNat).foldl execInstrBr s)
      Riscv.publicKeyBase key := memBits_of_mem_eq mem' hpk
  unfold decisionPrefix
  rw [List.foldl_append]
  generalize (constant .x7 Riscv.publicKeyBase.toNat).foldl execInstrBr s = u at x7 x18' hroot' hpk'
  constructor
  · simp only [List.foldl_cons, List.foldl_nil, execInstrBr, MachineState.getReg_setPC,
      MachineState.getMem_setPC, MachineState.getMem_setReg, MachineState.getReg_setReg_ne,
      MachineState.getReg_setReg_eq, l128, l136, l0, l8, l1, x7, x18', BitVec.add_zero, ne_eq,
      reduceCtorEq, not_false_eq_true]
    rw [addr136, words_equal, getMem_of_memBits (by decide) rootAddr_aligned hroot',
      getMem_of_memBits (by decide) publicKey_aligned0 hpk',
      high_word rootAddr_aligned8 hroot', high_word publicKey_aligned8 hpk']
    simp only [split128_equal]
  · simp only [List.foldl_cons, List.foldl_nil, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq, ne_eq, reduceCtorEq, not_false_eq_true, getReg_x0, l0,
      BitVec.add_zero]

open scoped Classical in
/-- After the root hash, the decision block halts with the specified verdict. -/
theorem decision_refines (s : MachineState) (answer : BitVec 256) (fuel : ℕ)
    (x18 : s.getReg .x18 = scratchAddr) (located : Riscv.CodeAt s s.pc decision)
    (hroot : MemBits s (scratchAddr + BitVec.ofNat 64 128) answer)
    (hpk : MemBits s Riscv.publicKeyBase pk) (bound : decision.length ≤ fuel) :
    Riscv.Refines fuel s (pure (some (decide (answer.setWidth 128 = pk)))) decision.length := by
  have root128 : MemBits s (scratchAddr + BitVec.ofNat 64 128) (answer.setWidth 128) := by
    have h := memBits_extract (start := 0) (len := 128) hroot (by decide) (by decide)
    rw [show scratchAddr + BitVec.ofNat 64 128 + BitVec.ofNat 64 (0 / 8) =
      scratchAddr + BitVec.ofNat 64 128 from BitVec.add_zero _] at h
    rw [BitVec.setWidth_eq_extractLsb' (by decide)]
    exact h
  rw [decision_parts] at located bound
  rw [decision_length]
  have ready := decisionPrefix_ready s x18
  have rest : Riscv.CodeAt (decisionPrefix.foldl execInstrBr s)
      (decisionPrefix.foldl execInstrBr s).pc [.ECALL] := by
    rw [Riscv.linear_fold_pc _ _ ready]
    exact located.append_right.code_eq (Riscv.fold_code _ _)
  obtain ⟨result, call⟩ := decisionPrefix_effect s (answer.setWidth 128) pk x18 root128 hpk
  have enough : decisionPrefix.length + 1 ≤ fuel := by simpa using bound
  rw [show fuel = decisionPrefix.length + ((fuel - decisionPrefix.length - 1) + 1) by omega,
    show (12 : ℕ) = decisionPrefix.length + 1 by rw [decisionPrefix_length]]
  apply Riscv.Refines.linear _ located.append_left ready
  exact Riscv.Refines.halt _ rest.head call
    (result.trans (congrArg (fun b : Bool => BitVec.ofNat 64 b.toNat) (decide_eq_decide.mpr Iff.rfl)))

/-! ## Root and decision together -/

theorem update_rc_ev {inst : DecidableEq (Fin graph.size)} (x : graph.Assignment)
    (v : BitVec (graph.len rc.fin)) (l : Fin 7) :
    @Function.update _ _ inst x rc.fin v (ev l).fin = x (ev l).fin :=
  Function.update_of_ne (fin_ne_of_ne (by simp)) _ _

open scoped Classical in
theorem rootDecision_refines (s : MachineState) (x : graph.Assignment) (cursor fuel : ℕ)
    (done : SubtreesDone index payload pk s x cursor)
    (located : Riscv.CodeAt s s.pc (root ++ decision)) (bound : root.length + decision.length ≤ fuel) :
    Riscv.Refines fuel s (runNodes' index payload [rc, rh] x cursor >>= fun r =>
        pure (some (decide ((r.1 rh.fin).setWidth 128 = pk))))
      (root.length + 1 + decision.length) := by
  obtain ⟨ctx, held⟩ := done
  simp only [runNodes', bind_assoc, pure_bind, cursorStep_rc, cursorStep_rh, Prod.mk.eta]
  set x' := Function.update x rc.fin
    ((tw rh ++ cat7 fun l => Forest.trunc (x (ev l).fin)).cast (graph_len_fin rc).symm) with hx'
  have inner : (fun l : Fin 7 => Forest.trunc (x' (ev l).fin)) =
      fun l => Forest.trunc (x (ev l).fin) := by
    funext l
    rw [hx', Function.update_of_ne (fin_ne_of_ne (by simp : ev l ≠ rc))]
  have tagged : x' rc.fin =
      (tw rh ++ cat7 fun l => Forest.trunc (x' (ev l).fin)).cast (graph_len_fin rc).symm := by
    rw [inner, hx', Function.update_self]
  have held' : ∀ l : Fin 7, HoldsE s l (x' (ev l).fin) := by
    intro l
    rw [hx', update_rc_ev]
    exact held l
  obtain ⟨ready, w10, w11, w12, wRegs, wFrame, wValue⟩ := rootLin_effect s ctx.regs x' held' tagged
  have located0 := located
  rw [root_parts, List.append_assoc] at located
  set w := rootLin.foldl execInstrBr s with hw
  have wPc : w.pc = s.pc + BitVec.ofNat 64 (4 * rootLin.length) := Riscv.linear_fold_pc s _ ready
  have wCode : Riscv.CodeAt w w.pc ([Instr.ECALL] ++ decision) := by
    rw [wPc]; exact located.append_right.code_eq (Riscv.fold_code s _)
  have wCodeEq : w.code = s.code := Riscv.fold_code s _
  have wFetch : w.code w.pc = some .ECALL := wCode.head
  have wCall : w.getReg .x5 = Riscv.hashCall := by
    rw [wRegs .x5 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact ctx.regs.call
  have wValid : Riscv.hashArgumentsValid w = true := by
    simp only [Riscv.hashArgumentsValid, w10, w11, w12, Bool.and_eq_true]
    refine ⟨⟨⟨⟨?_, rootAddr_access⟩, ?_⟩, ?_⟩, ?_⟩
    · show isValidOutputRange scratchAddr 114 = true
      exact scratch_output_range_114
    · exact scratch_word_access 136 (by decide) (by decide)
    · exact scratch_word_access 144 (by decide) (by decide)
    · exact scratch_word_access 152 (by decide) (by decide)
  have wInput : Riscv.hashInput w = ⟨graph.len rc.fin, x' rc.fin⟩ :=
    hashInput_of_memBits w10 (by rw [w11, rc_len]; rfl) wValue
  have blocks : blockCost paperParams (graph.len rc.fin) = 2 := by rw [rc_len]; decide
  rw [root_length] at bound ⊢
  rw [show rootLin.length + 1 + 1 + decision.length = rootLin.length + (2 + decision.length) by omega,
    show fuel = rootLin.length + ((fuel - rootLin.length - 1) + 1) by omega]
  apply Riscv.Refines.linear _ located.append_left ready
  rw [← hw]
  simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp_apply, pure_bind]
  have step := Riscv.Refines.hash (fuel := fuel - rootLin.length - 1) wFetch wCall wValid
    (k := fun y => pure (some (decide (((Function.update x' rh.fin (y.cast (graph_len_fin rh).symm)) rh.fin).setWidth 128 = pk))))
    (c := decision.length) ?_
  · rw [wInput, blocks] at step
    exact step
  intro y
  set v := Riscv.writeHash w y with hv
  have v18 : v.getReg .x18 = scratchAddr := by
    rw [hv, writeHash_regs, wRegs .x18 (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact ctx.regs.scratch
  have vPc : v.pc = s.pc + BitVec.ofNat 64 (4 * (rootLin.length + 1)) := by
    rw [hv, writeHash_pc, wPc, show (4 : Word) = BitVec.ofNat 64 4 from rfl, pcAdd,
      show 4 * rootLin.length + 4 = 4 * (rootLin.length + 1) by omega]
  have vCode : v.code = s.code := by rw [hv, writeHash_code, wCodeEq]
  have vLocated : Riscv.CodeAt v v.pc decision := by
    rw [vPc, ← root_length]
    exact located0.append_right.code_eq vCode
  have vRoot : MemBits v (scratchAddr + BitVec.ofNat 64 128) y := by
    have h := writeHash_memBits w y (by rw [w12]; exact rootAddr_aligned)
    rw [w12] at h
    exact h
  have vPk : MemBits v Riscv.publicKeyBase pk := by
    apply Direct.memBits_of_word_frame s v _ pk ctx.context.publicKey
    intro i hi
    change i < 128 at hi
    rw [hv, writeHash_frame _ _ _ (by
      rw [w12]
      intro j hj h
      have h' := congrArg BitVec.toNat h
      rw [alignToDword_toNat] at h'
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat, publicKey_toNat, scratchAddr_toNat] at h'
      omega)]
    apply wFrame
    rw [alignToDword_toNat]
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, publicKey_toNat]
    unfold scratchBase
    omega
  rw [Function.update_self]
  have cast_setWidth :
      ((y.cast (graph_len_fin rh).symm : BitVec (graph.len rh.fin)).setWidth 128) = y.setWidth 128 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth]
    rfl
  rw [cast_setWidth]
  exact decision_refines pk v y _ v18 vLocated vRoot vPk (by rw [decision_length] at *; omega)

end OptimalOTS.RiscvUpperProgram.Compact
