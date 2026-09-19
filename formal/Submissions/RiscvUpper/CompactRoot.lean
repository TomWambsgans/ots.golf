import Submissions.RiscvUpper.CompactSubtrees

/-! The root hash and the accept/reject decision of the compact image. -/

namespace OptimalOTS.RiscvUpperProgram.Compact

open RiscvZkvm.Rv64 Forest Forest.Name RiscvUpperForest.ForestVerifier OracleComp

set_option allowUnsafeReducibility true
attribute [local reducible] Forest.graph
attribute [local irreducible] Forest.fixedPositions Forest.fixedDigits

variable (index : Idx paperParams) (payload : List Bool) (pk : PublicKey paperParams)

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
  nodeTag_literal .rh

theorem cat7_assoc (v : Fin 7 → BitVec 128) :
    cat7 v = v 0 ++ (v 1 ++ (v 2 ++ (v 3 ++ (v 4 ++ (v 5 ++ v 6))))) := by
  simp only [cat7, BitVec.append_assoc, BitVec.cast_eq]

/-- The linear part of the root block. -/
def rootLin : Code :=
  copy128 .x21 (subtreeSlot 6) .x18 0 ++ copy128 .x21 (subtreeSlot 5) .x18 16 ++
  copy128 .x21 (subtreeSlot 4) .x18 32 ++ copy128 .x21 (subtreeSlot 3) .x18 48 ++
  copy128 .x21 (subtreeSlot 2) .x18 64 ++ copy128 .x21 (subtreeSlot 1) .x18 80 ++
  copy128 .x21 (subtreeSlot 0) .x18 96 ++ writeTag (BitVec.ofNat 16 2794) 112 ++
  [.ADDI .x10 .x18 0, .ADDI .x11 .x0 912, .ADDI .x12 .x18 128]

theorem root_parts : root = rootLin ++ [Instr.ECALL] := by decide +kernel
theorem root_length : root.length = rootLin.length + 1 := by rw [root_parts]; simp

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
        ((writeTag (BitVec.ofNat 16 2794) 112).foldl execInstrBr
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
  have r8 : Riscv.LinearReady s7 (writeTag (BitVec.ofNat 16 2794) 112) :=
    tag_scratch_ready s7 _ 112 (by decide) (by decide) x18₇
  set s8 := (writeTag (BitVec.ofNat 16 2794) 112).foldl execInstrBr s7 with hs8
  have g8 : ∀ r, r ≠ .x26 → s8.getReg r = s7.getReg r := fun r h26 =>
    writeTag_register s7 _ _ r h26
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
      apply (memBits_cast _ _ _ _).mpr
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
    apply memBits_of_word_frame s v _ pk ctx.context.publicKey
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
