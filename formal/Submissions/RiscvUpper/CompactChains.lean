import Submissions.RiscvUpper.CompactBlocks
import Submissions.RiscvUpper.SweepRefines

/-!
# One chain of the compact image

Chain `k` is one machine block: a prologue that copies the chain's disclosed word into its slot,
points HASH at the slot and jumps into a table of fourteen hash steps at the step of the disclosed
position, followed by the table. The specification visits the chain's nodes in the same order:
the nodes below the disclosed position are pure (zero or the disclosed read) and the nodes from
the position on issue one hash per level.
-/

namespace OptimalOTS.RiscvUpperProgram.Compact

open RiscvZkvm.Rv64 Forest Forest.Name RiscvUpperForest.ForestVerifier OracleComp

set_option allowUnsafeReducibility true
attribute [local reducible] Forest.graph
attribute [local irreducible] Forest.fixedPositions Forest.fixedDigits

variable (index : Idx paperParams) (payload : List Bool) (pk : PublicKey paperParams)

abbrev pos (k : Fin 63) : ℕ := (fixedPositions index k).val

/-- Machine facts at the end of the chain phase, handed to the tree phase. -/
structure ChainCtx (s : MachineState) (cursor : ℕ) (rem : List Name) : Prop where
  context : ExecutionContext s index payload pk
  regs : ChainRegs s
  atCursor : CursorAt s cursor
  aligned : cursor % 128 = 0
  budget : cursor + (rem.map (consumedBits index)).sum ≤ 5248

/-- Chain `k`'s slot currently represents `v`. -/
def Holds (s : MachineState) (k : Fin 63) {w : ℕ} (v : BitVec w) : Prop := MemBits s (slotAddr k) v

theorem slotAddr_word_ne (k k' : Fin 63) (hk : k.val < 36) (hk' : k'.val < 36) (i j : ℕ)
    (hi : i < 4) (hj : j < 4) (different : k ≠ k') :
    slotAddr k + BitVec.ofNat 64 (8 * i) ≠ slotAddr k' + BitVec.ofNat 64 (8 * j) := by
  intro h
  have h' := congrArg BitVec.toNat h
  simp only [slotAddr, chainSlot, chainsBase, BitVec.toNat_add, BitVec.toNat_ofNat] at h'
  have : k.val = k'.val := by omega
  exact different (Fin.ext this)

/-- Words of another chain's slot are untouched by writes into slot `k`. -/
theorem Holds.frame {s t : MachineState} {k k' : Fin 63} (hk : k.val < 36) (hk' : k'.val < 36)
    (different : k' ≠ k) {w : ℕ} (v : BitVec w) (small : w ≤ 256)
    (frame : ∀ addr, (∀ j, j < 4 → addr ≠ slotAddr k + BitVec.ofNat 64 (8 * j)) →
      t.getMem addr = s.getMem addr)
    (held : Holds s k' v) : Holds t k' v := by
  apply memBits_of_word_frame s t _ v held
  intro i hi
  apply frame
  intro j hj
  rw [aligned_bit_word _ ((aligned_iff _).mp (slotAddr_aligned k' hk')) i
    (by rw [slotAddr_toNat k' hk']; unfold chainsBase chainSlot; omega)]
  exact slotAddr_word_ne k' k hk' hk (i / 64) j (by omega) hj different

/-- Writes into chain slots preserve everything below the chain array. -/
theorem frameInputs_of_slot {s t : MachineState} {k : Fin 63} (hk : k.val < 36)
    (frame : ∀ addr, (∀ j, j < 4 → addr ≠ slotAddr k + BitVec.ofNat 64 (8 * j)) →
      t.getMem addr = s.getMem addr) : FrameInputs s t := by
  intro addr below
  apply frame
  intro j hj h
  have h' := congrArg BitVec.toNat h
  simp only [slotAddr, chainSlot, chainsBase, BitVec.toNat_add, BitVec.toNat_ofNat] at h'
  unfold chainsBase at below
  omega

/-! ## The specification's chain steps -/

theorem disclosed_src (k : Fin 63) :
    disclosed (fixedPositions index) (src k) = decide (k.val < 36 ∧ pos index k = 0) := rfl

theorem cursorStep_src (k : Fin 63) (x : graph.Assignment) (cursor : ℕ) :
    cursorStep index payload x cursor (src k) =
      if k.val < 36 ∧ pos index k = 0 then
        pure (Function.update x (src k).fin
          (ofBits (graph.len (src k).fin) ((payload.drop cursor).take (graph.len (src k).fin))),
          cursor + 128)
      else pure (Function.update x (src k).fin 0, cursor) := by
  unfold cursorStep
  simp only [disclosed_src, evaluated, Bool.false_eq_true, if_false, decide_eq_true_eq]
  rfl

theorem cursorStep_ci (k : Fin 63) (t : Fin 14) (x : graph.Assignment) (cursor : ℕ) :
    cursorStep index payload x cursor (ci k t) =
      if k.val < 36 ∧ pos index k ≤ t.val then
        pure (Function.update x (ci k t).fin
          ((tw (ch k t) ++ Forest.trunc (x (prev k t).fin)).cast (graph_len_fin (ci k t)).symm), cursor)
      else pure (Function.update x (ci k t).fin 0, cursor) := by
  unfold cursorStep
  simp only [disclosed, Bool.false_eq_true, if_false, evaluated, decide_eq_true_eq]
  split_ifs
  · rw [runOp_eq]
    simp only [evalName, map_pure, detVal_ci]
  · rfl

theorem cursorStep_ch (k : Fin 63) (t : Fin 14) (x : graph.Assignment) (cursor : ℕ) :
    cursorStep index payload x cursor (ch k t) =
      if k.val < 36 ∧ pos index k ≤ t.val then
        (fun y =>
          (Function.update x (ch k t).fin (y.cast (graph_len_fin (ch k t)).symm), cursor)) <$>
          hash paperParams (x (ci k t).fin)
      else pure (Function.update x (ch k t).fin 0, cursor) := by
  unfold cursorStep
  simp only [disclosed, Bool.false_eq_true, if_false, evaluated, decide_eq_true_eq]
  split_ifs
  · rw [runOp_eq]
    simp only [evalName, Functor.map_map]
  · rfl

theorem disclosed_cv (k : Fin 63) (t : Fin 14) :
    disclosed (fixedPositions index) (cv k t) = decide (k.val < 36 ∧ pos index k = t.val + 1) := rfl

theorem detVal_cv (k : Fin 63) (t : Fin 14) (x : graph.Assignment) :
    detVal (.cv k t) x = Forest.trunc (x (ch k t).fin) := rfl

theorem cursorStep_cv (k : Fin 63) (t : Fin 14) (x : graph.Assignment) (cursor : ℕ) :
    cursorStep index payload x cursor (cv k t) =
      if k.val < 36 ∧ pos index k = t.val + 1 then
        pure (Function.update x (cv k t).fin
          (ofBits (graph.len (cv k t).fin) ((payload.drop cursor).take (graph.len (cv k t).fin))),
          cursor + 128)
      else if k.val < 36 ∧ pos index k ≤ t.val then
        pure (Function.update x (cv k t).fin
          ((Forest.trunc (x (ch k t).fin)).cast (graph_len_fin (cv k t)).symm), cursor)
      else pure (Function.update x (cv k t).fin 0, cursor) := by
  unfold cursorStep
  simp only [disclosed_cv, evaluated, decide_eq_true_eq]
  split_ifs
  · rfl
  · rw [runOp_eq]
    simp only [evalName, map_pure, detVal_cv]
  · rfl

/-! ## Small facts about names and values -/

theorem fin_ne_of_ne {m n : Name} (h : m ≠ n) : m.fin ≠ n.fin :=
  fun e => h (Name.fin_injective e)

theorem cv_len_le (k : Fin 63) (t : Fin 14) : graph.len (cv k t).fin ≤ 256 := by
  rw [graph_len_fin]; norm_num [Name.len]

theorem ci_len (k : Fin 63) (t : Fin 14) : graph.len (ci k t).fin = 144 := graph_len_fin (ci k t)

/-- A represented graph value yields its low 128 bits. -/
theorem Holds.trunc {s : MachineState} {k : Fin 63} {n : Name} {x : graph.Assignment}
    (held : Holds s k (x n.fin)) : Holds s k (Forest.trunc (x n.fin)) := by
  have bound : 0 + 128 ≤ graph.len n.fin := by
    rw [graph_len_fin]
    exact node_length_positive n
  have h := memBits_extract (start := 0) (len := 128) held (by decide) bound
  have he : (x n.fin).extractLsb' 0 128 = Forest.trunc (x n.fin) := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp [Forest.trunc, hi]
  rw [show slotAddr k + BitVec.ofNat 64 (0 / 8) = slotAddr k from BitVec.add_zero _, he] at h
  exact h

/-- The word read for a 128-bit node is the specification's decoded value. -/
theorem read_value (k : Fin 63) (n : Name) (hn : graph.len n.fin = 128) (cursor : ℕ)
    (t : MachineState) (held : MemBits t (slotAddr k) (ofBits 128 (payload.drop cursor))) :
    Holds t k (ofBits (graph.len n.fin) ((payload.drop cursor).take (graph.len n.fin))) := by
  unfold Holds
  rw [hn]
  have take : ofBits 128 ((payload.drop cursor).take 128) = ofBits 128 (payload.drop cursor) := by
    simpa only [List.drop_zero] using
      ofBits_drop_take (payload.drop cursor) (cap := 128) (start := 0) (len := 128) (by decide)
  rw [take]
  exact held

theorem writeHash_regs (w : MachineState) (a : BitVec 256) (r : Reg) :
    (Riscv.writeHash w a).getReg r = w.getReg r := by
  simp [Riscv.writeHash]

theorem writeHash_code (w : MachineState) (a : BitVec 256) :
    (Riscv.writeHash w a).code = w.code := by
  simp [Riscv.writeHash]

theorem writeHash_pc (w : MachineState) (a : BitVec 256) :
    (Riscv.writeHash w a).pc = w.pc + 4 := rfl

theorem slotAddr_access (k : Fin 63) (hk : k.val < 36) (j : ℕ) (hj : j < 4) :
    isValidDwordAccess (slotAddr k + BitVec.ofNat 64 (8 * j)) = true := by
  rw [slotAddr_word]
  exact chain_access k j hk hj

theorem slotAddr_access0 (k : Fin 63) (hk : k.val < 36) :
    isValidDwordAccess (slotAddr k) = true := by
  have h := slotAddr_access k hk 0 (by decide)
  rwa [Nat.mul_zero, BitVec.add_zero] at h

theorem slotAddr_access8 (k : Fin 63) (hk : k.val < 36) :
    isValidDwordAccess (slotAddr k + 8) = true := by
  have h := slotAddr_access k hk 1 (by decide)
  rwa [show BitVec.ofNat 64 (8 * 1) = (8 : Word) from rfl] at h

theorem slotAddr_access16 (k : Fin 63) (hk : k.val < 36) :
    isValidDwordAccess (slotAddr k + 16) = true := by
  have h := slotAddr_access k hk 2 (by decide)
  rwa [show BitVec.ofNat 64 (8 * 2) = (16 : Word) from rfl] at h

theorem slotAddr_access24 (k : Fin 63) (hk : k.val < 36) :
    isValidDwordAccess (slotAddr k + 24) = true := by
  have h := slotAddr_access k hk 3 (by decide)
  rwa [show BitVec.ofNat 64 (8 * 3) = (24 : Word) from rfl] at h

theorem pcAdd (p : Word) (a b : ℕ) :
    p + BitVec.ofNat 64 a + BitVec.ofNat 64 b = p + BitVec.ofNat 64 (a + b) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add]

theorem mem_support_hash {n : ℕ} (u : BitVec n) (y : BitVec 256) :
    y ∈ support (hash paperParams u) := by
  have h : support (hash paperParams u) = Set.univ := by simp [OptimalOTS.hash]
  rw [h]
  exact Set.mem_univ y

/-! ## Code shapes -/

/-- The three nodes of level `t` of chain `k`. -/
def tripleN (k : Fin 63) (t : ℕ) : List Name :=
  if h : t < 14 then [ci k ⟨t, h⟩, ch k ⟨t, h⟩, cv k ⟨t, h⟩] else []

theorem chainNodes_eq (k : Fin 63) :
    chainNodes k = src k :: (List.range 14).flatMap (tripleN k) := by
  simp only [chainNodes, tripleN, List.finRange, List.range]
  rfl

theorem range_split (p : ℕ) (hp : p ≤ 14) :
    List.range 14 = List.range p ++ List.range' p (14 - p) := by
  have h := @List.range'_append_1 0 p (14 - p)
  rw [Nat.zero_add, Nat.add_sub_cancel' hp] at h
  rw [List.range_eq_range', List.range_eq_range', h]

theorem chainTag_toNat (k t : ℕ) (hk : k < 36) (ht : t < 14) :
    (BitVec.ofNat 16 (43 * k + 2 + 3 * t)).toNat = 43 * k + 2 + 3 * t := by
  rw [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (by omega)

theorem chainStep_eq (k t : ℕ) (hk : k < 36) (ht : t < 14) :
    chainStep k t = [.ADDI .x26 .x0 (BitVec.ofNat 12 (43 * k + 2 + 3 * t)),
      .SH .x18 .x26 (BitVec.ofNat 12 (chainSlot k + 16)), .ECALL] := by
  simp only [chainStep, writeTag, chainTag_toNat k t hk ht,
    constant_small .x26 (43 * k + 2 + 3 * t) (by omega)]
  rfl

theorem chainStep_length (k t : ℕ) (hk : k < 36) (ht : t < 14) : (chainStep k t).length = 3 := by
  rw [chainStep_eq k t hk ht]
  rfl

theorem steps_length (k : ℕ) (hk : k < 36) (l : List ℕ) (hl : ∀ t ∈ l, t < 14) :
    (l.flatMap (chainStep k)).length = 3 * l.length := by
  rw [List.length_flatMap]
  rw [List.map_congr_left (fun t ht => chainStep_length k t hk (hl t ht))]
  simp [List.map_const', List.sum_replicate]
  omega

theorem table_split (k : ℕ) (hk : k < 36) (p : ℕ) (hp : p ≤ 14) :
    chainTable k = (List.range p).flatMap (chainStep k) ++ (List.range' p (14 - p)).flatMap (chainStep k) := by
  rw [chainTable, range_split p hp, List.flatMap_append]

theorem table_prefix_length (k : ℕ) (hk : k < 36) (p : ℕ) (hp : p ≤ 14) :
    ((List.range p).flatMap (chainStep k)).length = 3 * p := by
  rw [steps_length k hk _ (fun t ht => by have := List.mem_range.mp ht; omega), List.length_range]

theorem chainTable_length (k : ℕ) (hk : k < 36) : (chainTable k).length = 42 := by
  rw [chainTable, steps_length k hk _ (fun t ht => List.mem_range.mp ht), List.length_range]

/-- The straight-line part of the prologue, between the address capture and the jump. -/
def prologueLinear (k : ℕ) : Code :=
  copy128 .x9 (16 * k) .x18 (chainSlot k) ++
  [.ADDI .x10 .x18 (BitVec.ofNat 12 (chainSlot k)), .ADDI .x12 .x18 (BitVec.ofNat 12 (chainSlot k)),
   .LD .x26 .x8 (BitVec.ofNat 12 (8 * k)),
   .SLLI .x27 .x26 3, .SLLI .x26 .x26 2, .ADD .x27 .x27 .x26,
   .ADD .x27 .x27 .x28]

theorem chainPrologue_parts (k : ℕ) :
    chainPrologue k = [.AUIPC .x28 0] ++ (prologueLinear k ++ [.JALR .x0 .x27 52]) := by
  simp [chainPrologue, prologueLinear]

theorem prologueLinear_length (k : ℕ) : (prologueLinear k).length = 11 := rfl

theorem chainPrologue_length (k : ℕ) : (chainPrologue k).length = 13 := rfl

theorem chainBlock_length (k : ℕ) (hk : k < 36) : (chainBlock k).length = 55 := by
  rw [chainBlock, List.length_append, chainPrologue_length, chainTable_length k hk]

/-- Landing inside a located block. -/
theorem CodeAt.drop {s : MachineState} {pc : Word} {code : List Instr}
    (located : Riscv.CodeAt s pc code) (i : ℕ) :
    Riscv.CodeAt s (pc + BitVec.ofNat 64 (4 * i)) (code.drop i) := by
  intro n hn
  have h := located (i + n) (by rw [List.length_drop] at hn; omega)
  rw [List.getElem?_drop, ← h, Nat.mul_add, BitVec.ofNat_add, BitVec.add_assoc]

/-- An even address is unchanged by clearing its low bit. -/
theorem and_not_one_of_even (a : Word) (h : a.toNat % 2 = 0) : a &&& ~~~(1#64) = a := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_one]
  by_cases hi0 : i = 0
  · subst hi0
    have h0 : a.getLsbD 0 = false := by
      rw [BitVec.getLsbD, Nat.testBit_zero]
      simp [h]
    rw [h0]
    decide
  · simp [hi0, hi]

/-! ## The prologue -/

theorem auipc_transition (s : MachineState) (fetch : s.code s.pc = some (.AUIPC .x28 0)) :
    RiscvZkvm.Rv64.step s = some (execInstrBr s (.AUIPC .x28 0)) := by
  rw [RiscvZkvm.Rv64.step, fetch]

theorem auipc_effect (s : MachineState) :
    (execInstrBr s (.AUIPC .x28 0)).getReg .x28 = s.pc ∧
    (∀ r, r ≠ .x28 → (execInstrBr s (.AUIPC .x28 0)).getReg r = s.getReg r) ∧
    (execInstrBr s (.AUIPC .x28 0)).mem = s.mem ∧
    (execInstrBr s (.AUIPC .x28 0)).pc = s.pc + 4 ∧
    (execInstrBr s (.AUIPC .x28 0)).code = s.code := by
  refine ⟨?_, ?_, rfl, rfl, rfl⟩
  · show s.pc + ((BitVec.ofNat 20 0).zeroExtend 32 <<< 12).signExtend 64 = s.pc
    rw [show ((BitVec.ofNat 20 0).zeroExtend 32 <<< 12).signExtend 64 = 0#64 by decide]
    exact BitVec.add_zero _
  · intro r h28
    simp only [execInstrBr, MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ .x28 r _ h28.symm]

theorem jalr_transition (s : MachineState) (fetch : s.code s.pc = some (.JALR .x0 .x27 52)) :
    RiscvZkvm.Rv64.step s = some (s.setPC ((s.getReg .x27 + signExtend12 52) &&& ~~~(1#64))) := by
  rw [RiscvZkvm.Rv64.step, fetch]
  rfl

/-- The effect of the straight-line prologue on registers and memory. -/
theorem prologueLinear_effect (a : MachineState) (k : ℕ) (hk : k < 36) :
    ((prologueLinear k).foldl execInstrBr a).getReg .x10 = a.getReg .x18 + BitVec.ofNat 64 (chainSlot k) ∧
    ((prologueLinear k).foldl execInstrBr a).getReg .x12 = a.getReg .x18 + BitVec.ofNat 64 (chainSlot k) ∧
    ((prologueLinear k).foldl execInstrBr a).getReg .x27 =
      (((copy128 .x9 (16 * k) .x18 (chainSlot k)).foldl execInstrBr a).getMem
          (a.getReg .x8 + BitVec.ofNat 64 (8 * k)) <<< 3) +
      (((copy128 .x9 (16 * k) .x18 (chainSlot k)).foldl execInstrBr a).getMem
          (a.getReg .x8 + BitVec.ofNat 64 (8 * k)) <<< 2) + a.getReg .x28 ∧
    (∀ r, r ≠ .x10 → r ≠ .x12 → r ≠ .x26 → r ≠ .x27 →
      ((prologueLinear k).foldl execInstrBr a).getReg r = a.getReg r) ∧
    ((prologueLinear k).foldl execInstrBr a).mem =
      ((copy128 .x9 (16 * k) .x18 (chainSlot k)).foldl execInstrBr a).mem := by
  have hslot : chainSlot k < 2048 := by unfold chainSlot; omega
  generalize hc : (copy128 .x9 (16 * k) .x18 (chainSlot k)).foldl execInstrBr a = c
  have unfolded : (prologueLinear k).foldl execInstrBr a =
      execInstrBr (execInstrBr (execInstrBr (execInstrBr (execInstrBr
      (execInstrBr (execInstrBr c (.ADDI .x10 .x18 (BitVec.ofNat 12 (chainSlot k))))
        (.ADDI .x12 .x18 (BitVec.ofNat 12 (chainSlot k))))
        (.LD .x26 .x8 (BitVec.ofNat 12 (8 * k)))) (.SLLI .x27 .x26 3)) (.SLLI .x26 .x26 2))
        (.ADD .x27 .x27 .x26)) (.ADD .x27 .x27 .x28) := by
    rw [← hc]
    simp only [prologueLinear, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have c8 : c.getReg .x8 = a.getReg .x8 := by
    rw [← hc]; exact copy128_reg a .x9 .x18 .x8 _ _ (by decide) (by decide)
  have c18 : c.getReg .x18 = a.getReg .x18 := by
    rw [← hc]; exact copy128_reg a .x9 .x18 .x18 _ _ (by decide) (by decide)
  have c28 : c.getReg .x28 = a.getReg .x28 := by
    rw [← hc]; exact copy128_reg a .x9 .x18 .x28 _ _ (by decide) (by decide)
  have cr : ∀ r, r ≠ .x26 → r ≠ .x27 → c.getReg r = a.getReg r := by
    intro r h26 h27
    rw [← hc]; exact copy128_reg a .x9 .x18 r _ _ h26 h27
  rw [unfolded]
  simp only [execInstrBr, signExtend12_nonnegative _ hslot,
    signExtend12_nonnegative _ (by omega : 8 * k < 2048)]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ .x27 .x10 _ (by decide),
      MachineState.getReg_setReg_ne _ .x26 .x10 _ (by decide),
      MachineState.getReg_setReg_ne _ .x12 .x10 _ (by decide),
      MachineState.getReg_setReg_eq (by decide : Reg.x10 ≠ .x0), c18]
  · simp only [MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ .x27 .x12 _ (by decide),
      MachineState.getReg_setReg_ne _ .x26 .x12 _ (by decide),
      MachineState.getReg_setReg_eq (by decide : Reg.x12 ≠ .x0),
      MachineState.getReg_setReg_ne _ .x10 .x18 _ (by decide), c18]
  · simp only [MachineState.getReg_setPC, MachineState.getReg_setReg_eq (by decide : Reg.x27 ≠ .x0),
      MachineState.getReg_setReg_eq (by decide : Reg.x26 ≠ .x0),
      MachineState.getReg_setReg_ne _ .x26 .x27 _ (by decide),
      MachineState.getReg_setReg_ne _ .x27 .x26 _ (by decide),
      MachineState.getReg_setReg_ne _ .x27 .x28 _ (by decide),
      MachineState.getReg_setReg_ne _ .x26 .x28 _ (by decide),
      MachineState.getReg_setReg_ne _ .x12 .x28 _ (by decide),
      MachineState.getReg_setReg_ne _ .x10 .x28 _ (by decide),
      MachineState.getReg_setReg_ne _ .x12 .x8 _ (by decide),
      MachineState.getReg_setReg_ne _ .x10 .x8 _ (by decide),
      MachineState.getMem_setPC, MachineState.getMem_setReg, c8, c28]
    rfl
  · intro r h10 h12 h26 h27
    simp only [MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ .x27 r _ h27.symm,
      MachineState.getReg_setReg_ne _ .x26 r _ h26.symm,
      MachineState.getReg_setReg_ne _ .x12 r _ h12.symm,
      MachineState.getReg_setReg_ne _ .x10 r _ h10.symm, cr r h26 h27]
  · rfl

/-- The prologue's loads and stores are valid: the payload word and the slot. -/
theorem payload_access (k j : ℕ) (hk : k < 36) (hj : j < 2) :
    isValidDwordAccess (Riscv.signatureBase + 16 + signExtend12 (BitVec.ofNat 12 (16 * k + 8 * j))) = true := by
  rw [signExtend12_nonnegative _ (by omega)]
  have hs : (Riscv.signatureBase + 16 + BitVec.ofNat 64 (16 * k + 8 * j)).toNat =
      4194368 + (16 * k + 8 * j) := by
    have hb : (Riscv.signatureBase + 16).toNat = 4194368 := by decide
    rw [BitVec.toNat_add, hb, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]
  simp only [isValidDwordAccess, isAligned8, isValidMemAddr, MEM_START, MEM_END,
    INPUT_MEM_START, INPUT_MEM_END, RAM_MEM_START, RAM_MEM_END, hs, Bool.and_eq_true,
    Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq]
  omega

theorem prologueLinear_ready (a : MachineState) (k : ℕ) (hk : k < 36)
    (base : a.getReg .x18 = BitVec.ofNat 64 chainsBase)
    (cursor : a.getReg .x9 = Riscv.signatureBase + 16)
    (positions : a.getReg .x8 = BitVec.ofNat 64 positionsBase) :
    Riscv.LinearReady a (prologueLinear k) := by
  have hslot : chainSlot k < 2048 := by unfold chainSlot; omega
  refine (copy128_ready a .x9 .x18 (16 * k) (chainSlot k) (by decide) (by decide) (by decide)
    ?_ ?_ ?_ ?_).append ?_
  · rw [cursor]
    simpa only [Nat.mul_zero, Nat.add_zero] using payload_access k 0 hk (by decide)
  · rw [cursor]
    simpa only [Nat.mul_one] using payload_access k 1 hk (by decide)
  · rw [signExtend12_nonnegative _ hslot, base]
    simpa only [Nat.mul_zero, Nat.add_zero] using chain_access k 0 hk (by decide)
  · rw [signExtend12_nonnegative _ (by unfold chainSlot; omega), base]
    simpa only [Nat.mul_one] using chain_access k 1 hk (by decide)
  · refine ⟨rfl, trivial, rfl, trivial, rfl, ?_, rfl, trivial, rfl, trivial, rfl, trivial, rfl,
      trivial, trivial⟩
    change isValidDwordAccess (_ + signExtend12 (BitVec.ofNat 12 (8 * k))) = true
    simp only [execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ .x12 .x8 _ (by decide),
      MachineState.getReg_setReg_ne _ .x10 .x8 _ (by decide),
      copy128_reg a .x9 .x18 .x8 _ _ (by decide) (by decide)]
    rw [signExtend12_nonnegative _ (by omega), positions]
    exact position_access ⟨k, by omega⟩

/-! ## Invariants within a chain -/

/-- Machine facts holding throughout chain `k`'s block after its prologue. -/
structure StepInv (s : MachineState) (x : graph.Assignment) (k : Fin 63) : Prop where
  context : ExecutionContext s index payload pk
  regs : ChainRegs s
  cursorReg : s.getReg .x9 = Riscv.signatureBase + 16
  pointer : s.getReg .x10 = slotAddr k
  pointer' : s.getReg .x12 = slotAddr k
  pcAligned : s.pc.toNat % 4 = 0
  done : ∀ k' : Fin 63, k'.val < 36 → k'.val < k.val → Holds s k' (x (cv k' 13).fin)

/-- The node holding chain `k`'s value at position `t`, for `t ≤ 14`. -/
def valueNode (k : Fin 63) (t : ℕ) : Name :=
  if t = 0 then src k else if h : t ≤ 14 then cv k ⟨t - 1, by omega⟩ else rh

theorem valueNode_zero (k : Fin 63) : valueNode k 0 = src k := by simp [valueNode]

theorem valueNode_succ (k : Fin 63) (t : Fin 14) : valueNode k (t.val + 1) = cv k t := by
  have h : t.val + 1 ≤ 14 := by omega
  simp only [valueNode, Nat.succ_ne_zero, if_false, dif_pos h, Nat.add_sub_cancel]

theorem prev_eq_valueNode (k : Fin 63) (t : Fin 14) : prev k t = valueNode k t.val := by
  unfold prev valueNode
  by_cases h0 : t.val = 0
  · rw [dif_pos h0, if_pos h0]
  · rw [dif_neg h0, if_neg h0, dif_pos (by omega)]

theorem valueNode_len (k : Fin 63) (t : ℕ) (ht : t ≤ 14) : graph.len (valueNode k t).fin = 128 := by
  unfold valueNode
  split_ifs <;> first | exact graph_len_fin _ | omega

/-! ## One hash step -/

/-- The three specification steps of level `t` of an evaluated chain, as one hash. -/
def tripleUpdate (x : graph.Assignment) (k : Fin 63) (t : Fin 14) (y : BitVec 256) :
    graph.Assignment :=
  Function.update (Function.update (Function.update x (ci k t).fin
      ((tw (ch k t) ++ Forest.trunc (x (prev k t).fin)).cast (graph_len_fin (ci k t)).symm))
    (ch k t).fin (y.cast (graph_len_fin (ch k t)).symm))
    (cv k t).fin ((Forest.trunc (y.cast (graph_len_fin (ch k t)).symm)).cast (graph_len_fin (cv k t)).symm)

theorem triple_run (k : Fin 63) (hk : k.val < 36) (t : Fin 14) (ht : pos index k ≤ t.val)
    (x : graph.Assignment) (cursor : ℕ) :
    runNodes' index payload [ci k t, ch k t, cv k t] x cursor =
      hash paperParams ((tw (ch k t) ++ Forest.trunc (x (prev k t).fin)).cast
          (graph_len_fin (ci k t)).symm) >>= fun y => pure (tripleUpdate x k t y, cursor) := by
  have hev : k.val < 36 ∧ pos index k ≤ t.val := ⟨hk, ht⟩
  have hnd : ¬ (k.val < 36 ∧ pos index k = t.val + 1) := fun h => by omega
  simp only [runNodes', cursorStep_ci, cursorStep_ch, cursorStep_cv, if_pos hev, if_neg hnd,
    pure_bind, bind_assoc, map_eq_bind_pure_comp, Function.comp_def, Function.update_self,
    tripleUpdate]

theorem tripleUpdate_cv (x : graph.Assignment) (k : Fin 63) (t : Fin 14) (y : BitVec 256) :
    tripleUpdate x k t y (cv k t).fin =
      (Forest.trunc (y.cast (graph_len_fin (ch k t)).symm)).cast (graph_len_fin (cv k t)).symm := by
  simp only [tripleUpdate, Function.update_self]

theorem tripleUpdate_ch (x : graph.Assignment) (k : Fin 63) (t : Fin 14) (y : BitVec 256) :
    tripleUpdate x k t y (ch k t).fin = y.cast (graph_len_fin (ch k t)).symm := by
  simp only [tripleUpdate]
  rw [Function.update_of_ne (fin_ne_of_ne (by simp)), Function.update_self]

theorem tripleUpdate_other (x : graph.Assignment) (k : Fin 63) (t : Fin 14) (y : BitVec 256)
    (n : Name) (h1 : n ≠ ci k t) (h2 : n ≠ ch k t) (h3 : n ≠ cv k t) :
    tripleUpdate x k t y n.fin = x n.fin := by
  simp only [tripleUpdate]
  rw [Function.update_of_ne (fin_ne_of_ne h3), Function.update_of_ne (fin_ne_of_ne h2),
    Function.update_of_ne (fin_ne_of_ne h1)]

theorem writeTag_ready (n : MachineState) (k : Fin 63) (hk : k.val < 36) (tag : BitVec 16)
    (base : n.getReg .x18 = BitVec.ofNat 64 chainsBase) :
    Riscv.LinearReady n (writeTag tag (chainSlot k + 16)) := by
  apply (constant_ready _ _ _).append
  refine ⟨rfl, ?_, trivial⟩
  change isValidHalfwordAccess (_ + signExtend12 (BitVec.ofNat 12 (chainSlot k + 16))) = true
  rw [signExtend12_nonnegative _ (by unfold chainSlot; omega),
    constant_preserves _ .x26 .x18 _ (by decide), base]
  exact chain_half_access k hk

theorem chainStep_parts (k : Fin 63) (t : Fin 14) :
    chainStep k t = writeTag (tw (ch k t)) (chainSlot k + 16) ++ [.ECALL] := rfl

theorem writeTag_length_small (k : Fin 63) (hk : k.val < 36) (t : Fin 14) :
    (writeTag (tw (ch k t)) (chainSlot k + 16)).length = 2 := by
  have := chainStep_length k t hk t.isLt
  rw [chainStep_parts, List.length_append] at this
  simpa using this

/-- Level `t` of chain `k`: the tag store and the hash, at three cycles. -/
theorem step_refines (k : Fin 63) (hk : k.val < 36) (t : Fin 14) (ht : pos index k ≤ t.val)
    (tail : Code) (K : graph.Assignment × ℕ → OracleComp (Spec paperParams) (Option Bool))
    (c budget cursor : ℕ) (s : MachineState) (x : graph.Assignment) (fuel : ℕ)
    (inv : StepInv index payload pk s x k) (held : Holds s k (x (prev k t).fin))
    (located : Riscv.CodeAt s s.pc (chainStep k t ++ tail)) (bound : 3 + budget ≤ fuel)
    (continuation : ∀ (u : MachineState) (y : BitVec 256),
      StepInv index payload pk u (tripleUpdate x k t y) k →
      Holds u k (tripleUpdate x k t y (cv k t).fin) → Riscv.CodeAt u u.pc tail →
      ∀ left, budget ≤ left → Riscv.Refines left u (K (tripleUpdate x k t y, cursor)) c) :
    Riscv.Refines fuel s (runNodes' index payload [ci k t, ch k t, cv k t] x cursor >>= K) (3 + c) := by
  rw [triple_run index payload k hk t ht]
  simp only [bind_assoc, pure_bind]
  have tagLen := writeTag_length_small k hk t
  rw [chainStep_parts, List.append_assoc] at located
  have ready := writeTag_ready s k hk (tw (ch k t)) inv.regs.base
  set w := (writeTag (tw (ch k t)) (chainSlot k + 16)).foldl execInstrBr s with hw
  have wPc : w.pc = s.pc + BitVec.ofNat 64 8 := by
    rw [hw, Riscv.linear_fold_pc s _ ready, tagLen]
  have wCode : Riscv.CodeAt w w.pc ([Instr.ECALL] ++ tail) := by
    rw [wPc, show (8 : ℕ) = 4 * (writeTag (tw (ch k t)) (chainSlot k + 16)).length by
      rw [tagLen]]
    exact located.append_right.code_eq (Riscv.fold_code s _)
  have wCodeEq : w.code = s.code := Riscv.fold_code s _
  have wRegs : ∀ r, r ≠ .x26 → w.getReg r = s.getReg r := fun r h => by
    rw [hw]; exact writeTag_register _ _ _ r h
  have wMem : w.mem = (s.setHalfword (s.getReg .x18 + BitVec.ofNat 64 (chainSlot k + 16))
      (tw (ch k t))).mem := by
    rw [hw]
    exact writeTag_memory s _ _ (by unfold chainSlot; omega) (nodeTag_literal (ch k t))
  have wFetch : w.code w.pc = some .ECALL := wCode.head
  have wCall : w.getReg .x5 = Riscv.hashCall := by rw [wRegs .x5 (by decide)]; exact inv.regs.call
  have wLen : w.getReg .x11 = 144 := by rw [wRegs .x11 (by decide)]; exact inv.regs.length
  have wSlot : w.getReg .x10 = slotAddr k := by rw [wRegs .x10 (by decide)]; exact inv.pointer
  have wSlot' : w.getReg .x12 = slotAddr k := by rw [wRegs .x12 (by decide)]; exact inv.pointer'
  have range : isValidOutputRange (slotAddr k) (((144 : Word).toNat + 7) / 8) = true := by
    show isValidOutputRange (slotAddr k) 18 = true
    exact chain_output_range ⟨k, hk⟩
  have wValid : Riscv.hashArgumentsValid w = true := by
    simp only [Riscv.hashArgumentsValid, wSlot, wSlot', wLen, Bool.and_eq_true]
    exact ⟨⟨⟨⟨range, slotAddr_access0 k hk⟩, slotAddr_access8 k hk⟩, slotAddr_access16 k hk⟩,
      slotAddr_access24 k hk⟩
  -- the query is the specification's chain input
  have heldS : MemBits s (s.getReg .x18 + BitVec.ofNat 64 (chainSlot k))
      (Forest.trunc (x (prev k t).fin)) := by
    rw [inv.regs.base]
    exact held.trunc
  have appended := tag_append s (chainSlot k) (Forest.trunc (x (prev k t).fin)) (tw (ch k t))
    (by decide) (by decide) (nodeTag_literal (ch k t)) (by unfold chainSlot; omega)
    (by unfold chainSlot; omega) (by rw [inv.regs.base]; decide) (by rw [inv.regs.base]; decide) heldS
  have wInput : Riscv.hashInput w = ⟨graph.len (ci k t).fin,
      (tw (ch k t) ++ Forest.trunc (x (prev k t).fin)).cast (graph_len_fin (ci k t)).symm⟩ := by
    apply hashInput_of_memBits wSlot
    · rw [wLen, ci_len]; rfl
    · apply (memBits_cast _ _ _ _).mpr
      rw [hw]
      have h := appended
      rw [inv.regs.base] at h
      exact h
  have blocks : blockCost paperParams (graph.len (ci k t).fin) = 1 := by
    rw [ci_len]; decide
  -- compose: tag store, hash, continuation
  rw [show fuel = (writeTag (tw (ch k t)) (chainSlot k + 16)).length + ((fuel - 3) + 1) by
      rw [tagLen]; omega,
    show 3 + c = (writeTag (tw (ch k t)) (chainSlot k + 16)).length + (1 + c) by
      rw [tagLen]; omega]
  apply Riscv.Refines.linear _ located.append_left ready
  rw [← hw]
  have step := Riscv.Refines.hash (fuel := fuel - 3) wFetch wCall wValid
    (k := fun y => K (tripleUpdate x k t y, cursor)) (c := c) ?_
  · rw [wInput, blocks] at step
    exact step
  intro y
  set v := Riscv.writeHash w y with hv
  have vRegs : ∀ r, r ≠ .x26 → v.getReg r = s.getReg r := by
    intro r h26
    rw [hv, writeHash_regs, wRegs r h26]
  have slotFrame : ∀ addr, (∀ j, j < 4 → addr ≠ slotAddr k + BitVec.ofNat 64 (8 * j)) →
      v.getMem addr = s.getMem addr := by
    intro addr outside
    rw [hv, writeHash_frame _ _ _ (by rw [wSlot']; exact outside)]
    have hw' : w.getMem addr = (s.setHalfword (s.getReg .x18 + BitVec.ofNat 64 (chainSlot k + 16))
        (tw (ch k t))).getMem addr := by
      simp only [MachineState.getMem, wMem]
    rw [hw', MachineState.setHalfword]
    have tagWord : alignToDword (s.getReg .x18 + BitVec.ofNat 64 (chainSlot k + 16)) =
        slotAddr k + BitVec.ofNat 64 (8 * 2) := by
      rw [inv.regs.base, slotAddr_word, show chainSlot k + 8 * 2 = chainSlot k + 16 by omega]
      exact aligned_offset _ (by decide) _ (by unfold chainSlot; omega)
        (by simp only [BitVec.toNat_ofNat, chainsBase, chainSlot]; omega)
    rw [MachineState.getMem_setMem_ne (by rw [tagWord]; exact outside 2 (by decide))]
  have vPc : v.pc = s.pc + BitVec.ofNat 64 12 := by
    rw [hv, writeHash_pc, wPc]
    rw [show (4 : Word) = BitVec.ofNat 64 4 from rfl, pcAdd]
  have vCode : v.code = s.code := by rw [hv, writeHash_code, wCodeEq]
  have vLocated : Riscv.CodeAt v v.pc tail := by
    rw [vPc, show (12 : ℕ) = 4 * (writeTag (tw (ch k t)) (chainSlot k + 16) ++ [Instr.ECALL]).length by
      rw [List.length_append, tagLen]; rfl]
    have h : Riscv.CodeAt s s.pc ((writeTag (tw (ch k t)) (chainSlot k + 16) ++ [Instr.ECALL]) ++ tail) := by
      simpa only [List.append_assoc] using located
    exact h.append_right.code_eq vCode
  have answer : Holds v k ((y.cast (graph_len_fin (ch k t)).symm : BitVec (graph.len (ch k t).fin))) := by
    unfold Holds
    apply (memBits_cast _ _ _ _).mpr
    have h := writeHash_memBits w y (by rw [wSlot']; exact slotAddr_aligned k hk)
    rw [wSlot'] at h
    exact h
  have chHeld : Holds v k (tripleUpdate x k t y (ch k t).fin) := by
    rw [tripleUpdate_ch]; exact answer
  have cvHeld : Holds v k (tripleUpdate x k t y (cv k t).fin) := by
    rw [tripleUpdate_cv]
    unfold Holds
    apply (memBits_cast _ _ _ _).mpr
    have h := chHeld.trunc
    rwa [tripleUpdate_ch] at h
  have vAligned : v.pc.toNat % 4 = 0 := by
    rw [vPc, BitVec.toNat_add, BitVec.toNat_ofNat]
    have := inv.pcAligned
    rw [Nat.mod_mod_of_dvd _ (by norm_num : 4 ∣ 2 ^ 64)]
    omega
  apply continuation v y ?_ cvHeld vLocated (fuel - 3) (by omega)
  refine ⟨inv.context.frameInputs (frameInputs_of_slot hk slotFrame) (vRegs .x8 (by decide)),
    ⟨by rw [vRegs .x18 (by decide)]; exact inv.regs.base,
     by rw [vRegs .x5 (by decide)]; exact inv.regs.call,
     by rw [vRegs .x11 (by decide)]; exact inv.regs.length⟩,
    by rw [vRegs .x9 (by decide)]; exact inv.cursorReg,
    by rw [vRegs .x10 (by decide)]; exact inv.pointer,
    by rw [vRegs .x12 (by decide)]; exact inv.pointer', vAligned, ?_⟩
  intro k' hk' hlt
  have same : k' ≠ k := fun h => by rw [h] at hlt; exact Nat.lt_irrefl _ hlt
  rw [tripleUpdate_other x k t y (cv k' 13) (by simp) (by simp)
    (fun h => same (Name.cv.inj h).1)]
  exact Holds.frame hk hk' same _ (cv_len_le k' 13) slotFrame (inv.done k' hk' hlt)

/-- Levels `t` to `13` of chain `k`. -/
theorem steps_refines (k : Fin 63) (hk : k.val < 36) (tail : Code)
    (K : graph.Assignment × ℕ → OracleComp (Spec paperParams) (Option Bool)) (c rest' cursor : ℕ)
    (continuation : ∀ (u : MachineState) (y : graph.Assignment),
      StepInv index payload pk u y k → Holds u k (y (cv k 13).fin) → Riscv.CodeAt u u.pc tail →
      ∀ left, rest' ≤ left → Riscv.Refines left u (K (y, cursor)) c) :
    ∀ (n t : ℕ), 14 - t = n → t ≤ 14 → pos index k ≤ t →
    ∀ (s : MachineState) (x : graph.Assignment) (fuel : ℕ),
      StepInv index payload pk s x k → Holds s k (x (valueNode k t).fin) →
      Riscv.CodeAt s s.pc ((List.range' t (14 - t)).flatMap (chainStep k) ++ tail) →
      3 * (14 - t) + rest' ≤ fuel →
      Riscv.Refines fuel s
        (runNodes' index payload ((List.range' t (14 - t)).flatMap (tripleN k)) x cursor >>= K)
        (3 * (14 - t) + c) := by
  intro n
  induction n with
  | zero =>
    intro t ht _ _ s x fuel inv held located bound
    have h14 : t = 14 := by omega
    subst h14
    simp only [Nat.sub_self, List.range'_zero, List.flatMap_nil, List.nil_append, runNodes',
      pure_bind, Nat.mul_zero, Nat.zero_add] at located bound ⊢
    have hv : valueNode k 14 = cv k 13 := by simp [valueNode]
    rw [hv] at held
    exact continuation s x inv held located fuel bound
  | succ n ih =>
    intro t hn ht hp s x fuel inv held located bound
    have ht' : t < 14 := by omega
    have hsucc : 14 - t = (14 - (t + 1)) + 1 := by omega
    rw [hsucc] at located bound ⊢
    rw [List.range'_succ, List.flatMap_cons, List.append_assoc] at located
    rw [List.range'_succ, List.flatMap_cons, runNodes'_append, bind_assoc]
    have triple : tripleN k t = [ci k ⟨t, ht'⟩, ch k ⟨t, ht'⟩, cv k ⟨t, ht'⟩] := by
      simp [tripleN, ht']
    rw [triple]
    rw [show 3 * (14 - (t + 1) + 1) + c = 3 + (3 * (14 - (t + 1)) + c) by omega]
    apply step_refines index payload pk k hk ⟨t, ht'⟩ hp
      (tail := (List.range' (t + 1) (14 - (t + 1))).flatMap (chainStep k) ++ tail)
      (fun r => runNodes' index payload ((List.range' (t + 1) (14 - (t + 1))).flatMap (tripleN k))
        r.1 r.2 >>= K)
      (3 * (14 - (t + 1)) + c) (3 * (14 - (t + 1)) + rest') cursor s x fuel inv
      (by rwa [prev_eq_valueNode]) located (by omega)
    intro u y inv' held' located' left hleft
    exact ih (t + 1) (by omega) (by omega) (by omega) u _ left inv'
      (by rw [show t + 1 = (⟨t, ht'⟩ : Fin 14).val + 1 from rfl, valueNode_succ]; exact held')
      located' (by omega)

/-! ## Between chains -/

/-- Machine facts holding between chain blocks: chains before `k` are complete. -/
structure ChainsInv (s : MachineState) (x : graph.Assignment) (k : ℕ) : Prop where
  context : ExecutionContext s index payload pk
  regs : ChainRegs s
  cursorReg : s.getReg .x9 = Riscv.signatureBase + 16
  pcAligned : s.pc.toNat % 4 = 0
  done : ∀ k' : Fin 63, k'.val < 36 → k'.val < k → Holds s k' (x (cv k' 13).fin)

/-! ## The specification before the disclosed level -/

/-- Before its disclosed level, a chain's nodes are pure: zeros, then the disclosed word. -/
theorem prefix_run (k : Fin 63) (hk : k.val < 36) :
    ∀ (q : ℕ), q ≤ pos index k → ∀ (x : graph.Assignment) (cursor : ℕ),
    ∃ x' : graph.Assignment,
      runNodes' index payload (src k :: (List.range q).flatMap (tripleN k)) x cursor =
        pure (x', if q = pos index k then cursor + 128 else cursor) ∧
      (∀ k' : Fin 63, k' ≠ k → x' (cv k' 13).fin = x (cv k' 13).fin) ∧
      (q = pos index k → x' (valueNode k q).fin =
        ofBits (graph.len (valueNode k q).fin)
          ((payload.drop cursor).take (graph.len (valueNode k q).fin))) := by
  intro q
  induction q with
  | zero =>
    intro _ x cursor
    have run : runNodes' index payload (src k :: (List.range 0).flatMap (tripleN k)) x cursor =
        cursorStep index payload x cursor (src k) := by
      simp only [List.range_zero, List.flatMap_nil, runNodes', Prod.mk.eta, bind_pure]
    rw [run, cursorStep_src, valueNode_zero]
    by_cases h0 : pos index k = 0
    · rw [if_pos ⟨hk, h0⟩, if_pos h0.symm]
      refine ⟨_, rfl, ?_, ?_⟩
      · intro k' _
        exact Function.update_of_ne (fin_ne_of_ne (by simp)) _ _
      · intro _
        rw [Function.update_self]
    · rw [if_neg (fun h => h0 h.2), if_neg (fun h => h0 h.symm)]
      refine ⟨_, rfl, ?_, ?_⟩
      · intro k' _
        exact Function.update_of_ne (fin_ne_of_ne (by simp)) _ _
      · intro h
        exact absurd h.symm h0
  | succ q ih =>
    intro hq x cursor
    obtain ⟨x₁, run₁, frame₁, _⟩ := ih (by omega) x cursor
    have hq14 : q < 14 := by
      have := (fixedPositions index k).isLt
      change q + 1 ≤ (fixedPositions index k).val at hq
      omega
    have hq' : ¬ (q = pos index k) := by omega
    have hnot : ¬ (k.val < 36 ∧ pos index k ≤ q) := fun h => by omega
    rw [if_neg hq'] at run₁
    have triple : tripleN k q = [ci k ⟨q, hq14⟩, ch k ⟨q, hq14⟩, cv k ⟨q, hq14⟩] := by
      simp [tripleN, hq14]
    have run : runNodes' index payload (src k :: (List.range (q + 1)).flatMap (tripleN k)) x cursor =
        runNodes' index payload [ci k ⟨q, hq14⟩, ch k ⟨q, hq14⟩, cv k ⟨q, hq14⟩] x₁ cursor := by
      rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, triple, ← List.cons_append,
        runNodes'_append, run₁, pure_bind]
    rw [run]
    simp only [runNodes', cursorStep_ci, cursorStep_ch, cursorStep_cv, if_neg hnot, pure_bind,
      Prod.mk.eta, bind_pure]
    have hv : valueNode k (q + 1) = cv k ⟨q, hq14⟩ := valueNode_succ k ⟨q, hq14⟩
    rw [hv]
    by_cases hd : pos index k = q + 1
    · rw [if_pos ⟨hk, hd⟩, if_pos hd.symm]
      refine ⟨_, rfl, ?_, ?_⟩
      · intro k' hk'
        rw [Function.update_of_ne (fin_ne_of_ne (fun h => hk' (Name.cv.inj h).1)),
          Function.update_of_ne (fin_ne_of_ne (by simp)),
          Function.update_of_ne (fin_ne_of_ne (by simp))]
        exact frame₁ k' hk'
      · intro _
        rw [Function.update_self]
    · rw [if_neg (fun h => hd h.2), if_neg (fun h => hd h.symm)]
      refine ⟨_, rfl, ?_, ?_⟩
      · intro k' hk'
        rw [Function.update_of_ne (fin_ne_of_ne (fun h => hk' (Name.cv.inj h).1)),
          Function.update_of_ne (fin_ne_of_ne (by simp)),
          Function.update_of_ne (fin_ne_of_ne (by simp))]
        exact frame₁ k' hk'
      · intro h
        exact absurd h.symm hd

/-! ## Inactive chains -/

/-- Nodes that are neither disclosed nor evaluated are pure and leave the cursor in place. -/
theorem inert_run (l : List Name)
    (inert : ∀ n ∈ l, disclosed (fixedPositions index) n = false ∧
      evaluated (fixedPositions index) n = false) :
    ∀ (x : graph.Assignment) (cursor : ℕ), ∃ x' : graph.Assignment,
      runNodes' index payload l x cursor = pure (x', cursor) ∧
      ∀ m : Name, m ∉ l → x' m.fin = x m.fin := by
  induction l with
  | nil => intro x cursor; exact ⟨x, rfl, fun _ _ => rfl⟩
  | cons n ns ih =>
    intro x cursor
    obtain ⟨hd, he⟩ := inert n (by simp)
    have step : cursorStep index payload x cursor n = pure (Function.update x n.fin 0, cursor) := by
      unfold cursorStep
      rw [hd, he]
      simp
    obtain ⟨x', run, frame⟩ := ih (fun m hm => inert m (by simp [hm])) (Function.update x n.fin 0) cursor
    refine ⟨x', ?_, ?_⟩
    · rw [runNodes', step, pure_bind]
      exact run
    · intro m hm
      have hmn : m ≠ n := fun h => hm (by simp [h])
      have hns : m ∉ ns := fun h => hm (by simp [h])
      rw [frame m hns, Function.update_of_ne (fin_ne_of_ne hmn)]

theorem inactive_inert (k : Fin 63) (hk : ¬ k.val < 36) :
    ∀ n ∈ chainNodes k, disclosed (fixedPositions index) n = false ∧
      evaluated (fixedPositions index) n = false := by
  intro n hn
  simp only [chainNodes, List.mem_cons, List.mem_flatMap, List.mem_finRange, true_and,
    List.mem_singleton, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | ⟨t, rfl | rfl | rfl⟩ <;> simp [disclosed, evaluated, hk]

/-- An inactive chain has no machine code and no oracle queries. -/
theorem inactive_refines (k : Fin 63) (hk : ¬ k.val < 36)
    (K : graph.Assignment × ℕ → OracleComp (Spec paperParams) (Option Bool))
    (x : graph.Assignment) (cursor : ℕ) (s : MachineState) (fuel c : ℕ)
    (continuation : ∀ y : graph.Assignment,
      (∀ k' : Fin 63, k'.val < 36 → y (cv k' 13).fin = x (cv k' 13).fin) →
      Riscv.Refines fuel s (K (y, cursor)) c) :
    Riscv.Refines fuel s (runNodes' index payload (chainNodes k) x cursor >>= K) c := by
  obtain ⟨y, run, frame⟩ := inert_run index payload (chainNodes k) (inactive_inert index k hk) x cursor
  rw [run, pure_bind]
  apply continuation y
  intro k' hk'
  apply frame
  intro h
  simp only [chainNodes, List.mem_cons, List.mem_flatMap, List.mem_finRange, true_and,
    List.mem_singleton, List.not_mem_nil, or_false] at h
  rcases h with h | ⟨t, h | h | h⟩
  · exact absurd h (by simp)
  · exact absurd h (by simp)
  · exact absurd h (by simp)
  · have e := (Name.cv.inj h).1
    rw [e] at hk'
    exact hk hk'

/-! ## The prologue of an active chain -/

/-- The prologue's copy changes only the first two words of slot `k`. -/
theorem prologue_copy_frame (a : MachineState) (k : Fin 63) (hk : k.val < 36)
    (base : a.getReg .x18 = BitVec.ofNat 64 chainsBase) (addr : Word)
    (outside : ∀ j, j < 4 → addr ≠ slotAddr k + BitVec.ofNat 64 (8 * j)) :
    ((copy128 .x9 (16 * k.val) .x18 (chainSlot k)).foldl execInstrBr a).getMem addr = a.getMem addr := by
  have hslot' : chainSlot k < 2048 := by unfold chainSlot; omega
  have hslot : chainSlot k + 8 < 2048 := by unfold chainSlot; omega
  rw [copy128_getMem _ _ _ _ _ (by decide) (by decide) (by decide)]
  simp only [signExtend12_nonnegative (16 * k.val) (by omega),
    signExtend12_nonnegative (16 * k.val + 8) (by omega),
    signExtend12_nonnegative (chainSlot k) hslot', signExtend12_nonnegative (chainSlot k + 8) hslot, base]
  have o0 : addr ≠ BitVec.ofNat 64 chainsBase + BitVec.ofNat 64 (chainSlot k) := by
    have := outside 0 (by decide)
    rwa [slotAddr_word, Nat.mul_zero, Nat.add_zero] at this
  have o1 : addr ≠ BitVec.ofNat 64 chainsBase + BitVec.ofNat 64 (chainSlot k + 8) := by
    have := outside 1 (by decide)
    rwa [slotAddr_word, Nat.mul_one] at this
  rw [if_neg o1, if_neg o0]

/-- The prologue's copy moves chain `k`'s disclosed word into its slot. -/
theorem prologue_copy_holds (a : MachineState) (k : Fin 63) (hk : k.val < 36)
    (base : a.getReg .x18 = BitVec.ofNat 64 chainsBase)
    (cursor : a.getReg .x9 = Riscv.signatureBase + 16)
    (payloadBits : MemBits a (Riscv.signatureBase + 16) (ofBits 5248 payload)) :
    Holds ((copy128 .x9 (16 * k.val) .x18 (chainSlot k)).foldl execInstrBr a) k
      (ofBits 128 (payload.drop (128 * k.val))) := by
  have source : MemBits a (a.getReg .x9 + BitVec.ofNat 64 (16 * k.val))
      (ofBits 128 (payload.drop (128 * k.val))) := by
    have h := memBits_extract (start := 128 * k.val) (len := 128) payloadBits (by omega) (by omega)
    rw [ofBits_extract payload (by omega), show 128 * k.val / 8 = 16 * k.val by omega, ← cursor] at h
    exact h
  have hslot : chainSlot k + 8 < 2048 := by unfold chainSlot; omega
  have srcAligned : alignToDword (a.getReg .x9 + BitVec.ofNat 64 (16 * k.val)) =
      a.getReg .x9 + BitVec.ofNat 64 (16 * k.val) := by
    rw [cursor]
    apply (aligned_iff _).mpr
    have hb : (Riscv.signatureBase + 16).toNat = 4194368 := by decide
    simp (disch := omega) only [BitVec.toNat_add, hb, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    omega
  have moved := copy128_memBits a .x9 .x18 (16 * k.val) (chainSlot k) (by decide) (by decide) (by decide)
    (by omega) hslot srcAligned (by rw [base]; exact slotAddr_aligned k hk) _ source
  rw [base] at moved
  exact moved

/-- The jump lands `52 + 12 p` bytes after the block start, an even address. -/
theorem jump_target (pc : Word) (p : ℕ) (_hp : p ≤ 14) (aligned : pc.toNat % 4 = 0) :
    ((BitVec.ofNat 64 p <<< 3) + (BitVec.ofNat 64 p <<< 2) + pc + signExtend12 52) &&& ~~~(1#64) =
      pc + BitVec.ofNat 64 (52 + 12 * p) := by
  have h52 : signExtend12 52 = BitVec.ofNat 64 52 := by decide
  have hpc := pc.isLt
  simp only [Nat.reducePow] at hpc
  have e : (BitVec.ofNat 64 p <<< 3) + (BitVec.ofNat 64 p <<< 2) + pc + signExtend12 52 =
      pc + BitVec.ofNat 64 (52 + 12 * p) := by
    rw [h52]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
      Nat.reducePow]
    omega
  rw [e]
  apply and_not_one_of_even
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_mod_of_dvd _ (by norm_num : 2 ∣ 2 ^ 64)]
  simp only [Nat.reducePow]
  omega

/-- Chain `k`'s prologue: the slot receives the disclosed word, the hash pointers are set, and
control jumps to the table entry of the disclosed level, at 13 cycles. -/
theorem prologue_refines (k : Fin 63) (hk : k.val < 36) (rest : Code) (s : MachineState)
    (x : graph.Assignment) (inv : ChainsInv index payload pk s x k.val)
    (located : Riscv.CodeAt s s.pc (chainPrologue k ++ rest))
    {fuel : ℕ} {q : OracleComp (Spec paperParams) (Option Bool)} {c : ℕ}
    (continuation : ∀ u : MachineState,
      StepInv index payload pk u x k → Holds u k (ofBits 128 (payload.drop (128 * k.val))) →
      u.code = s.code → u.pc = s.pc + BitVec.ofNat 64 (52 + 12 * pos index k) →
      Riscv.Refines fuel u q c) :
    Riscv.Refines (13 + fuel) s q (13 + c) := by
  have hp : pos index k ≤ 14 := by
    show (fixedPositions index k).val ≤ 14
    have := (fixedPositions index k).isLt
    omega
  rw [chainPrologue_parts, List.append_assoc, List.append_assoc, List.singleton_append] at located
  -- the address capture
  have fetchA : s.code s.pc = some (.AUIPC .x28 0) := located.head
  obtain ⟨a28, aRegs, aMem, aPc, aCode⟩ := auipc_effect s
  rw [show 13 + fuel = (12 + fuel) + 1 by omega, show 13 + c = (12 + c) + 1 by omega]
  apply Riscv.Refines.branch fetchA rfl (fun h => nomatch h) (auipc_transition s fetchA)
  set a := execInstrBr s (.AUIPC .x28 0) with ha
  have a18 : a.getReg .x18 = BitVec.ofNat 64 chainsBase := by
    rw [aRegs .x18 (by decide)]; exact inv.regs.base
  have a9 : a.getReg .x9 = Riscv.signatureBase + 16 := by
    rw [aRegs .x9 (by decide)]; exact inv.cursorReg
  have a8 : a.getReg .x8 = s.getReg .x8 := aRegs .x8 (by decide)
  -- the straight-line part
  have locatedA : Riscv.CodeAt a a.pc (prologueLinear k ++ ([Instr.JALR .x0 .x27 52] ++ rest)) := by
    rw [aPc]
    exact located.tail.code_eq aCode
  have readyA : Riscv.LinearReady a (prologueLinear k) :=
    prologueLinear_ready a k hk a18 a9 (by rw [a8]; exact inv.context.positionBase)
  rw [show 12 + fuel = (prologueLinear k).length + (1 + fuel) by rw [prologueLinear_length]; omega,
    show 12 + c = (prologueLinear k).length + (1 + c) by rw [prologueLinear_length]; omega]
  apply Riscv.Refines.linear _ locatedA.append_left readyA
  obtain ⟨w10, w12, w27, wRegs, wMem⟩ := prologueLinear_effect a k hk
  have wPc := Riscv.linear_fold_pc a _ readyA
  have wCodeA := Riscv.fold_code a (prologueLinear k)
  set w := (prologueLinear k).foldl execInstrBr a with hw
  set cp := (copy128 .x9 (16 * k.val) .x18 (chainSlot k)).foldl execInstrBr a with hcp
  have wCode : w.code = s.code := wCodeA.trans aCode
  have locatedW : Riscv.CodeAt w w.pc ([Instr.JALR .x0 .x27 52] ++ rest) := by
    rw [wPc]
    exact locatedA.append_right.code_eq wCodeA
  have fetchJ : w.code w.pc = some (.JALR .x0 .x27 52) := locatedW.head
  -- memory after the prologue
  have aFrame : ∀ addr, a.getMem addr = s.getMem addr := fun addr => by
    simp only [MachineState.getMem, aMem]
  have cpFrame : ∀ addr, (∀ j, j < 4 → addr ≠ slotAddr k + BitVec.ofNat 64 (8 * j)) →
      cp.getMem addr = s.getMem addr := by
    intro addr outside
    rw [hcp, prologue_copy_frame a k hk a18 addr outside, aFrame]
  have wFrame : ∀ addr, (∀ j, j < 4 → addr ≠ slotAddr k + BitVec.ofNat 64 (8 * j)) →
      w.getMem addr = s.getMem addr := by
    intro addr outside
    rw [← cpFrame addr outside]
    simp only [MachineState.getMem, wMem]
  have outsidePos : ∀ j, j < 4 →
      a.getReg .x8 + BitVec.ofNat 64 (8 * k.val) ≠ slotAddr k + BitVec.ofNat 64 (8 * j) := by
    intro j hj h
    have h' := congrArg BitVec.toNat h
    rw [a8, inv.context.positionBase] at h'
    simp (disch := omega) only [slotAddr, chainSlot, chainsBase, positionsBase, BitVec.toNat_add,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt] at h'
    omega
  have position : cp.getMem (a.getReg .x8 + BitVec.ofNat 64 (8 * k.val)) =
      BitVec.ofNat 64 (pos index k) := by
    rw [cpFrame _ outsidePos, a8]
    exact inv.context.positions k hk
  have target : (w.getReg .x27 + signExtend12 52) &&& ~~~(1#64) =
      s.pc + BitVec.ofNat 64 (52 + 12 * pos index k) := by
    rw [w27, position, a28]
    exact jump_target s.pc (pos index k) hp inv.pcAligned
  have landAligned : (s.pc + BitVec.ofNat 64 (52 + 12 * pos index k)).toNat % 4 = 0 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_mod_of_dvd _ (by norm_num : 4 ∣ 2 ^ 64)]
    have := inv.pcAligned
    simp only [Nat.reducePow]
    omega
  have wRegsS : ∀ r, r ≠ .x10 → r ≠ .x12 → r ≠ .x26 → r ≠ .x27 → r ≠ .x28 →
      w.getReg r = s.getReg r := by
    intro r h10 h12 h26 h27 h28
    rw [wRegs r h10 h12 h26 h27, aRegs r h28]
  -- the jump
  rw [Nat.add_comm 1 fuel, Nat.add_comm 1 c]
  apply Riscv.Refines.branch fetchJ rfl (fun h => nomatch h) (jalr_transition w fetchJ)
  rw [target]
  apply continuation (w.setPC (s.pc + BitVec.ofNat 64 (52 + 12 * pos index k))) ?_ ?_ wCode rfl
  · refine ⟨inv.context.frameInputs (frameInputs_of_slot hk (fun addr outside => ?_)) ?_,
      ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, landAligned, ?_⟩
    · simp only [MachineState.getMem_setPC]; exact wFrame addr outside
    · simp only [MachineState.getReg_setPC]
      exact wRegsS .x8 (by decide) (by decide) (by decide) (by decide) (by decide)
    · simp only [MachineState.getReg_setPC]
      rw [wRegsS .x18 (by decide) (by decide) (by decide) (by decide) (by decide)]
      exact inv.regs.base
    · simp only [MachineState.getReg_setPC]
      rw [wRegsS .x5 (by decide) (by decide) (by decide) (by decide) (by decide)]
      exact inv.regs.call
    · simp only [MachineState.getReg_setPC]
      rw [wRegsS .x11 (by decide) (by decide) (by decide) (by decide) (by decide)]
      exact inv.regs.length
    · simp only [MachineState.getReg_setPC]
      rw [wRegsS .x9 (by decide) (by decide) (by decide) (by decide) (by decide)]
      exact inv.cursorReg
    · simp only [MachineState.getReg_setPC]
      rw [w10, a18]
      rfl
    · simp only [MachineState.getReg_setPC]
      rw [w12, a18]
      rfl
    · intro k' hk' hlt
      exact Holds.frame hk hk' (fun h => by rw [h] at hlt; exact Nat.lt_irrefl _ hlt) _
        (cv_len_le k' 13)
        (fun addr outside => by simp only [MachineState.getMem_setPC]; exact wFrame addr outside)
        (inv.done k' hk' hlt)
  · exact memBits_of_mem_eq (show (w.setPC _).mem = cp.mem from wMem)
      (prologue_copy_holds payload a k hk a18 a9 (memBits_of_mem_eq aMem inv.context.payloadBits))

/-! ## One active chain -/

/-- One active chain: its prologue, then the levels from its disclosed position, at
`13 + 3 (14 - p)` cycles. -/
theorem chain_refines (k : Fin 63) (hk : k.val < 36) (tail : Code)
    (K : graph.Assignment × ℕ → OracleComp (Spec paperParams) (Option Bool)) (c rest' : ℕ)
    (continuation : ∀ (u : MachineState) (y : graph.Assignment),
      ChainsInv index payload pk u y (k.val + 1) → Riscv.CodeAt u u.pc tail →
      ∀ left, rest' ≤ left → Riscv.Refines left u (K (y, 128 * k.val + 128)) c)
    (s : MachineState) (x : graph.Assignment) (fuel : ℕ)
    (inv : ChainsInv index payload pk s x k.val)
    (located : Riscv.CodeAt s s.pc (chainBlock k ++ tail))
    (bound : 13 + 3 * (14 - pos index k) + rest' ≤ fuel) :
    Riscv.Refines fuel s (runNodes' index payload (chainNodes k) x (128 * k.val) >>= K)
      (13 + 3 * (14 - pos index k) + c) := by
  have hp : pos index k ≤ 14 := by
    show (fixedPositions index k).val ≤ 14
    have := (fixedPositions index k).isLt
    omega
  -- the specification up to the disclosed level is pure
  obtain ⟨x', run, frame, value⟩ := prefix_run index payload k hk (pos index k) le_rfl x (128 * k.val)
  rw [if_pos rfl] at run
  have nodes : chainNodes k = (src k :: (List.range (pos index k)).flatMap (tripleN k)) ++
      (List.range' (pos index k) (14 - pos index k)).flatMap (tripleN k) := by
    rw [chainNodes_eq, range_split (pos index k) hp, List.flatMap_append, List.cons_append]
  rw [nodes, runNodes'_append, run, bind_assoc, pure_bind]
  dsimp only
  -- the prologue
  rw [chainBlock, List.append_assoc] at located
  rw [show fuel = 13 + (fuel - 13) by omega,
    show 13 + 3 * (14 - pos index k) + c = 13 + (3 * (14 - pos index k) + c) by omega]
  apply prologue_refines index payload pk k hk (chainTable k ++ tail) s x inv located
  intro u inv' held code pc
  have locatedU : Riscv.CodeAt u u.pc
      ((List.range' (pos index k) (14 - pos index k)).flatMap (chainStep k) ++ tail) := by
    have h := CodeAt.drop located (13 + 3 * pos index k)
    have split : chainPrologue k ++ (chainTable k ++ tail) =
        (chainPrologue k ++ (List.range (pos index k)).flatMap (chainStep k)) ++
        ((List.range' (pos index k) (14 - pos index k)).flatMap (chainStep k) ++ tail) := by
      rw [table_split k hk (pos index k) hp]
      simp only [List.append_assoc]
    have hlen : (chainPrologue k ++ (List.range (pos index k)).flatMap (chainStep k)).length =
        13 + 3 * pos index k := by
      rw [List.length_append, chainPrologue_length, table_prefix_length k hk (pos index k) hp]
    rw [split, List.drop_left' hlen,
      show 4 * (13 + 3 * pos index k) = 52 + 12 * pos index k by omega, ← pc] at h
    exact h.code_eq code
  have inv'' : StepInv index payload pk u x' k := by
    refine ⟨inv'.context, inv'.regs, inv'.cursorReg, inv'.pointer, inv'.pointer', inv'.pcAligned, ?_⟩
    intro k' hk' hlt
    rw [frame k' (fun h => by rw [h] at hlt; exact Nat.lt_irrefl _ hlt)]
    exact inv'.done k' hk' hlt
  have held' : Holds u k (x' (valueNode k (pos index k)).fin) := by
    rw [value rfl]
    exact read_value payload k _ (valueNode_len k _ hp) _ u held
  apply steps_refines index payload pk k hk tail K c rest' (128 * k.val + 128) ?_
    (14 - pos index k) (pos index k) rfl hp le_rfl u x' (fuel - 13) inv'' held' locatedU (by omega)
  intro v y invV heldV locatedV left hleft
  apply continuation v y ?_ locatedV left hleft
  refine ⟨invV.context, invV.regs, invV.cursorReg, invV.pcAligned, ?_⟩
  intro k' hk' hlt
  rcases Nat.lt_or_ge k'.val k.val with lt | ge
  · exact invV.done k' hk' lt
  · have e : k' = k := Fin.ext (by omega)
    rw [e]
    exact heldV

end OptimalOTS.RiscvUpperProgram.Compact
