import Submissions.RiscvUpper.CompactBlocks
import Submissions.RiscvUpper.SweepRefines
import Submissions.RiscvUpper.NodeValueProof

/-! The chain phase of the compact image: sources, chain inputs, chain hashes and chain values. -/

namespace OptimalOTS.RiscvUpperProgram.Compact

open RiscvZkvm.Rv64 Forest Forest.Name RiscvUpperForest.ForestVerifier OracleComp

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option allowUnsafeReducibility true
attribute [local reducible] Forest.graph
attribute [local irreducible] Forest.fixedPositions Forest.fixedDigits

variable (index : Idx paperParams) (payload : List Bool) (pk : PublicKey paperParams)

/-- Position of chain `k` in the selected cut. -/
abbrev pos (k : Fin 63) : ℕ := (fixedPositions index k).val

/-- Machine facts at every node boundary of the chain phase. `rem` lists every node still to be
visited, in this segment and after it, so the cursor never leaves the payload. -/
structure ChainCtx (s : MachineState) (cursor : ℕ) (rem : List Name) : Prop where
  context : Direct.ExecutionContext s index payload pk
  regs : ChainRegs s
  atCursor : Direct.CursorAt s cursor
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
  apply Direct.memBits_of_word_frame s t _ v held
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

theorem readBlock_eval (p k : ℕ) (s : MachineState) :
    (readBlock p k).eval s =
      if PureBlock.passes true .x26 ((readPrefix p k).foldl execInstrBr s) then
        (readBody k).foldl execInstrBr
          (PureBlock.branchState true .x26 (readBody k).length ((readPrefix p k).foldl execInstrBr s))
      else PureBlock.branchState true .x26 (readBody k).length ((readPrefix p k).foldl execInstrBr s) := by
  simp only [readBlock, PureBlock.eval, PureBlock.code]
  try rfl

theorem readBlock_ready (p k : ℕ) (hp : p < 2048) (hk : k < 36) (s : MachineState)
    (base8 : s.getReg .x8 = BitVec.ofNat 64 positionsBase)
    (base18 : s.getReg .x18 = BitVec.ofNat 64 chainsBase) (cursor : Direct.CursorReady s) :
    (readBlock p k).Ready s := by
  refine ⟨readPrefix_ready s p k hp (by omega) base8, ?_, fun _ => ?_⟩
  · show (readBody k).length < 1023
    rw [readBody_length]
    decide
  have regs := (readPrefix_effect s p k hp (by omega)).2.1
  apply readBody_ready _ k hk
  · simp only [PureBlock.branchState, PureBlock.eval, MachineState.getReg_setPC,
      regs .x18 (by decide) (by decide)]
    exact base18
  · simpa only [Direct.CursorReady, PureBlock.branchState, PureBlock.eval,
      MachineState.getReg_setPC, regs .x9 (by decide) (by decide)] using cursor

/-- The prefix's flag is zero exactly when chain `k` sits at position `p`. -/
theorem readPrefix_test (p : ℕ) (hp : p < 15) (k : Fin 63) (hk : k.val < 36) (s : MachineState)
    (context : Direct.ExecutionContext s index payload pk) :
    PureBlock.passes true .x26 ((readPrefix p k).foldl execInstrBr s) ↔ pos index k = p := by
  have flag := (readPrefix_effect s p k (by omega) k.isLt).1
  have position := context.positions k hk
  unfold PureBlock.passes
  rw [decide_eq_true_iff, flag, position]
  change _ ^^^ _ = 0#64 ↔ _
  rw [BitVec.xor_eq_zero_iff]
  have hb := (fixedPositions index k).isLt
  exact ofNat_eq_iff _ _ (by omega) (by omega)

/-- The cycles of a guarded read: the whole block when the chain is disclosed at this level,
otherwise its three-instruction test and the branch. -/
def readCost (p : ℕ) (k : Fin 63) : ℕ := if pos index k = p then 9 else 4

theorem readChain_length (p k : ℕ) (hp : p < 2048) : (readChain p k).length = 9 := by
  have h := PureBlock.guard_code_length true .x26 (.linear (readBody k))
  simp only [PureBlock.code, if_true] at h
  rw [← readBlock_code]
  simp only [readBlock, PureBlock.code, if_true, List.length_append, readPrefix_length p k hp, h,
    readBody_length]

/-- The guarded read block either skips or copies the next payload word into slot `k`. -/
theorem readBlock_refines (p : ℕ) (hp : p < 15) (k : Fin 63) (hk : k.val < 36) (s : MachineState)
    (cursor : ℕ) (context : Direct.ExecutionContext s index payload pk) (regs : ChainRegs s)
    (atCursor : Direct.CursorAt s cursor) (aligned : cursor % 128 = 0)
    (bounded : cursor ≤ 5248) (room : pos index k = p → cursor + 128 ≤ 5248) (tail : Code)
    (located : Riscv.CodeAt s s.pc (readChain p k ++ tail))
    {fuel budget c : ℕ} (bound : (readChain p k).length + budget ≤ fuel)
    {q : OracleComp (Spec paperParams) (Option Bool)}
    (skip : pos index k ≠ p → ∀ t : MachineState, t.mem = s.mem →
      (∀ r, r ≠ .x26 → r ≠ .x27 → t.getReg r = s.getReg r) → Riscv.CodeAt t t.pc tail →
      ∀ left, budget ≤ left → Riscv.Refines left t q c)
    (read : pos index k = p → ∀ t : MachineState,
      MemBits t (slotAddr k) (ofBits 128 (payload.drop cursor)) →
      (∀ addr, (∀ j, j < 4 → addr ≠ slotAddr k + BitVec.ofNat 64 (8 * j)) →
        t.getMem addr = s.getMem addr) →
      t.getReg .x9 = s.getReg .x9 + 16 →
      (∀ r, r ≠ .x9 → r ≠ .x26 → r ≠ .x27 → t.getReg r = s.getReg r) →
      Riscv.CodeAt t t.pc tail → ∀ left, budget ≤ left → Riscv.Refines left t q c) :
    Riscv.Refines fuel s q (readCost index p k + c) := by
  have ready := readBlock_ready p k (by omega) hk s context.positionBase regs.base
    (atCursor.ready (by omega) aligned)
  have code := readBlock_code p k
  rw [← code] at located bound
  have costEq : (readBlock p k).cost s = readCost index p k := by
    have test := readPrefix_test index payload pk p hp k hk s context
    simp only [readBlock, PureBlock.cost, PureBlock.eval, readPrefix_length p k (by omega),
      readBody_length, readCost]
    by_cases hpos : pos index k = p
    · have passed := test.mpr hpos
      simp [hpos, passed]
    · have npassed : ¬ PureBlock.passes true .x26 ((readPrefix p k).foldl execInstrBr s) :=
        mt test.mp hpos
      simp [hpos, npassed]
  rw [← costEq]
  apply Riscv.Refines.block_exact (readBlock p k) s ready located.append_left budget fuel q c bound
  intro left hleft
  have pc := PureBlock.eval_pc (readBlock p k) s ready
  have codeEq := PureBlock.eval_code (readBlock p k) s
  have located' : Riscv.CodeAt ((readBlock p k).eval s) ((readBlock p k).eval s).pc tail := by
    rw [pc]
    exact located.append_right.code_eq codeEq
  obtain ⟨flag, prefixRegs, prefixMem⟩ := readPrefix_effect s p k (by omega) k.isLt
  have test := readPrefix_test index payload pk p hp k hk s context
  rw [readBlock_eval] at located' ⊢
  by_cases passed : PureBlock.passes true .x26 ((readPrefix p k).foldl execInstrBr s)
  · rw [if_pos passed] at located' ⊢
    have hpos := test.mp passed
    set u := PureBlock.branchState true .x26 (readBody k).length
      ((readPrefix p k).foldl execInstrBr s) with hu
    have uRegs : ∀ r, r ≠ .x26 → r ≠ .x27 → u.getReg r = s.getReg r := by
      intro r h26 h27
      simp only [hu, PureBlock.branchState, MachineState.getReg_setPC, prefixRegs r h26 h27]
    have uMem : u.mem = s.mem := by
      simp only [hu, PureBlock.branchState, MachineState.setPC, prefixMem]
    obtain ⟨bodyCursor, bodyRegs, bodyMem⟩ := readBody_effect u k hk
    have copied : ((readBody k).foldl execInstrBr u).mem =
        ((copy128 .x9 0 .x18 (chainSlot k)).foldl execInstrBr u).mem := bodyMem
    apply read hpos _ _ _ _ _ located' left hleft
    · -- the copied word
      have source : MemBits u (u.getReg .x9 + BitVec.ofNat 64 0) (ofBits 128 (payload.drop cursor)) := by
        rw [BitVec.add_zero, uRegs .x9 (by decide) (by decide)]
        exact memBits_of_mem_eq uMem (context.payload_word cursor atCursor aligned (room hpos))
      have uCursor : Direct.CursorReady u := by
        simpa only [Direct.CursorReady, uRegs .x9 (by decide) (by decide)] using
          atCursor.ready (by omega) aligned
      have hslot : chainSlot k + 8 < 2048 := by unfold chainSlot; omega
      have moved := copy128_memBits u .x9 .x18 0 (chainSlot k) (by decide) (by decide) (by decide)
        (by decide) hslot
        (by rw [BitVec.add_zero]; exact (aligned_iff _).mpr uCursor.2.2)
        (by rw [uRegs .x18 (by decide) (by decide), regs.base]; exact slotAddr_aligned k hk)
        (ofBits 128 (payload.drop cursor)) source
      rw [uRegs .x18 (by decide) (by decide), regs.base] at moved
      exact memBits_of_mem_eq copied moved
    · -- everything outside the slot's first two words
      intro addr outside
      change ((readBody k).foldl execInstrBr u).getMem addr = _
      have h : ((readBody k).foldl execInstrBr u).getMem addr =
          ((copy128 .x9 0 .x18 (chainSlot k)).foldl execInstrBr u).getMem addr := by
        simp only [MachineState.getMem, copied]
      have hslot' : chainSlot k < 2048 := by unfold chainSlot; omega
      have hslot : chainSlot k + 8 < 2048 := by unfold chainSlot; omega
      rw [h, copy128_getMem _ _ _ _ _ (by decide) (by decide) (by decide)]
      simp only [signExtend12_nonnegative 0 (by decide), signExtend12_nonnegative (0 + 8) (by decide),
        signExtend12_nonnegative (chainSlot k) hslot', signExtend12_nonnegative (chainSlot k + 8) hslot,
        uRegs .x18 (by decide) (by decide), regs.base]
      have o0 : addr ≠ BitVec.ofNat 64 chainsBase + BitVec.ofNat 64 (chainSlot k) := by
        have := outside 0 (by decide)
        rwa [slotAddr_word, Nat.mul_zero, Nat.add_zero] at this
      have o1 : addr ≠ BitVec.ofNat 64 chainsBase + BitVec.ofNat 64 (chainSlot k + 8) := by
        have := outside 1 (by decide)
        rwa [slotAddr_word, Nat.mul_one] at this
      rw [if_neg o1, if_neg o0]
      change u.getMem addr = s.getMem addr
      simp only [MachineState.getMem, uMem]
    · rw [bodyCursor, uRegs .x9 (by decide) (by decide)]
    · intro r h9 h26 h27
      rw [bodyRegs r h9 h26 h27, uRegs r h26 h27]
  · rw [if_neg passed] at located' ⊢
    have hpos := mt test.mpr passed
    apply skip hpos _ _ _ located' left hleft
    · simp only [PureBlock.branchState, MachineState.setPC, prefixMem]
    · intro r h26 h27
      simp only [PureBlock.branchState, MachineState.getReg_setPC, prefixRegs r h26 h27]


/-! ## Context transfer -/

variable {index} {payload} {pk}

theorem ChainCtx.bounded {s : MachineState} {cursor : ℕ} {rem : List Name}
    (ctx : ChainCtx index payload pk s cursor rem) : cursor ≤ 5248 := by
  have := ctx.budget
  omega

theorem ChainCtx.drop {s : MachineState} {cursor : ℕ} {n : Name} {rem : List Name}
    (ctx : ChainCtx index payload pk s cursor (n :: rem)) :
    ChainCtx index payload pk s cursor rem := by
  refine ⟨ctx.context, ctx.regs, ctx.atCursor, ctx.aligned, ?_⟩
  have := ctx.budget
  simp only [List.cons_append, List.map_cons, List.sum_cons] at this
  omega

/-- A node without disclosure leaves the machine data and cursor unchanged. -/
theorem ChainCtx.skip {s t : MachineState} {cursor : ℕ} {n : Name} {rem : List Name}
    (ctx : ChainCtx index payload pk s cursor (n :: rem)) (mem : t.mem = s.mem)
    (regs : ∀ r, r ≠ .x26 → r ≠ .x27 → t.getReg r = s.getReg r) :
    ChainCtx index payload pk t cursor rem := by
  have base := ctx.drop
  refine ⟨base.context.frameInputs (fun addr _ => by simp only [MachineState.getMem, mem])
    (regs .x8 (by decide) (by decide)), ⟨?_, ?_, ?_⟩, ?_, base.aligned, base.budget⟩
  · rw [regs .x18 (by decide) (by decide)]; exact base.regs.base
  · rw [regs .x5 (by decide) (by decide)]; exact base.regs.call
  · rw [regs .x11 (by decide) (by decide)]; exact base.regs.length
  · unfold Direct.CursorAt
    rw [regs .x9 (by decide) (by decide)]
    exact base.atCursor

/-- Reading one disclosed word advances the cursor by 128 bits. -/
theorem ChainCtx.read {s t : MachineState} {cursor : ℕ} {n : Name} {rem : List Name}
    (ctx : ChainCtx index payload pk s cursor (n :: rem)) (consumed : consumedBits index n = 128)
    (frame : FrameInputs s t)
    (regs : ∀ r, r ≠ .x9 → r ≠ .x26 → r ≠ .x27 → t.getReg r = s.getReg r)
    (cursorReg : t.getReg .x9 = s.getReg .x9 + 16) :
    ChainCtx index payload pk t (cursor + 128) rem := by
  refine ⟨ctx.context.frameInputs frame (regs .x8 (by decide) (by decide) (by decide)),
    ⟨?_, ?_, ?_⟩, ?_, by have := ctx.aligned; omega, ?_⟩
  · rw [regs .x18 (by decide) (by decide) (by decide)]; exact ctx.regs.base
  · rw [regs .x5 (by decide) (by decide) (by decide)]; exact ctx.regs.call
  · rw [regs .x11 (by decide) (by decide) (by decide)]; exact ctx.regs.length
  · unfold Direct.CursorAt
    rw [cursorReg, ctx.atCursor, show (cursor + 128) / 8 = cursor / 8 + 16 by omega,
      BitVec.ofNat_add, ← BitVec.add_assoc]
    rfl
  · have := ctx.budget
    simp only [List.cons_append, List.map_cons, List.sum_cons, consumed] at this
    omega

theorem ChainCtx.room {s : MachineState} {cursor : ℕ} {n : Name} {rem : List Name}
    (ctx : ChainCtx index payload pk s cursor (n :: rem)) (consumed : consumedBits index n = 128) :
    cursor + 128 ≤ 5248 := by
  have := ctx.budget
  simp only [List.cons_append, List.map_cons, List.sum_cons, consumed] at this
  omega

/-- Register changes of a whole hash block preserve the chain-phase context. -/
theorem ChainCtx.hashed {s t : MachineState} {cursor : ℕ} {n : Name} {rem : List Name}
    (ctx : ChainCtx index payload pk s cursor (n :: rem)) (frame : FrameInputs s t)
    (regs : ∀ r, r ≠ .x10 → r ≠ .x12 → r ≠ .x26 → t.getReg r = s.getReg r) :
    ChainCtx index payload pk t cursor rem := by
  have base := ctx.drop
  refine ⟨base.context.frameInputs frame (regs .x8 (by decide) (by decide) (by decide)),
    ⟨?_, ?_, ?_⟩, ?_, base.aligned, base.budget⟩
  · rw [regs .x18 (by decide) (by decide) (by decide)]; exact base.regs.base
  · rw [regs .x5 (by decide) (by decide) (by decide)]; exact base.regs.call
  · rw [regs .x11 (by decide) (by decide) (by decide)]; exact base.regs.length
  · unfold Direct.CursorAt
    rw [regs .x9 (by decide) (by decide) (by decide)]
    exact base.atCursor

/-! ## Sources -/

variable (index) (payload) (pk)

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

theorem consumedBits_src (k : Fin 63) :
    consumedBits index (src k) = if k.val < 36 ∧ pos index k = 0 then 128 else 0 := by
  rw [consumedBits_word, disclosed_src]
  by_cases h : k.val < 36 ∧ pos index k = 0 <;> simp [h]

def srcCode : Name → Code
  | .src k => if k.val < 36 then readChain 0 k.val else []
  | _ => []

def srcCost : Name → ℕ
  | .src k => if k.val < 36 then readCost index 0 k else 0
  | _ => 0

/-- Sources read so far hold their disclosed values. -/
def SrcInv (after : List Name) (s : MachineState) (x : graph.Assignment) (cursor : ℕ)
    (rem : List Name) : Prop :=
  ChainCtx index payload pk s cursor (rem ++ after) ∧
  ∀ k : Fin 63, k.val < 36 → pos index k = 0 → src k ∉ rem → Holds s k (x (src k).fin)

def srcSeg (after : List Name) : Segment := ⟨srcCode, srcCost index, SrcInv index payload pk after⟩

theorem src_fin_ne (k : Fin 63) (n : Name) (h : n ≠ src k) : n.fin ≠ (src k).fin :=
  fun e => h (Name.fin_injective e)

theorem fin_ne_of_ne {m n : Name} (h : m ≠ n) : m.fin ≠ n.fin :=
  fun e => h (Name.fin_injective e)

theorem src_len_le (k : Fin 63) : graph.len (src k).fin ≤ 256 := by
  rw [graph_len_fin]; norm_num [Name.len]

theorem cv_len_le (k : Fin 63) (t : Fin 14) : graph.len (cv k t).fin ≤ 256 := by
  rw [graph_len_fin]; norm_num [Name.len]

theorem ch_len_le (k : Fin 63) (t : Fin 14) : graph.len (ch k t).fin ≤ 256 := by
  rw [graph_len_fin]; norm_num [Name.len]

theorem prev_len_le (k : Fin 63) (t : Fin 14) : graph.len (prev k t).fin ≤ 256 := by
  unfold prev
  split_ifs <;> rw [graph_len_fin] <;> norm_num [Name.len]

theorem writeTag_le (tag : BitVec 16) (off : ℕ) : (Direct.writeTag tag off).length ≤ 3 := by
  unfold Direct.writeTag constant
  split_ifs <;> simp

theorem prev_ne_ci (k k' : Fin 63) (t : Fin 14) : prev k' t ≠ ci k t := by
  unfold prev; split_ifs <;> simp

theorem prev_ne_ch (k k' : Fin 63) (t : Fin 14) : prev k' t ≠ ch k t := by
  unfold prev; split_ifs <;> simp

theorem prev_ne_cv (k k' : Fin 63) (t : Fin 14) : prev k' t ≠ cv k t := by
  unfold prev
  split_ifs with h0
  · simp
  · simp only [ne_eq, Name.cv.injEq, not_and]
    intro _ e
    have := congrArg Fin.val e
    simp only at this
    omega

/-- A represented graph value yields its low 128 bits. -/
theorem Holds.trunc {s : MachineState} {k : Fin 63} {n : Name} {x : graph.Assignment}
    (held : Holds s k (x n.fin)) : Holds s k (Forest.trunc (x n.fin)) := by
  have bound : 0 + 128 ≤ graph.len n.fin := by
    rw [graph_len_fin]
    exact Direct.node_length_positive n
  have h := memBits_extract (start := 0) (len := 128) held (by decide) bound
  have he : (x n.fin).extractLsb' 0 128 = Forest.trunc (x n.fin) := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp [Forest.trunc, hi]
  rw [show slotAddr k + BitVec.ofNat 64 (0 / 8) = slotAddr k from BitVec.add_zero _, he] at h
  exact h

/-- The word read for a source is the specification's decoded value. -/
theorem src_value (k : Fin 63) (cursor : ℕ) (t : MachineState)
    (held : MemBits t (slotAddr k) (ofBits 128 (payload.drop cursor))) :
    Holds t k (ofBits (graph.len (src k).fin) ((payload.drop cursor).take (graph.len (src k).fin))) := by
  have length : graph.len (src k).fin = 128 := graph_len_fin (src k)
  unfold Holds
  rw [length]
  have take : ofBits 128 ((payload.drop cursor).take 128) = ofBits 128 (payload.drop cursor) := by
    simpa only [List.drop_zero] using
      ofBits_drop_take (payload.drop cursor) (cap := 128) (start := 0) (len := 128) (by decide)
  rw [take]
  exact held

theorem src_refines (after : List Name) (k : Fin 63) :
    (srcSeg index payload pk after).NodeRefines index payload (src k) := by
  by_cases hk : k.val < 36
  · intro s x cursor rest tail K c budget fuel _ inv located bound continuation
    obtain ⟨ctx, holds⟩ := inv
    have code : srcCode (src k) = readChain 0 k := by simp [srcCode, hk]
    have cost : srcCost index (src k) = readCost index 0 k := by simp [srcCost, hk]
    change Riscv.CodeAt s s.pc (srcCode (src k) ++ tail) at located
    change (srcCode (src k)).length + budget ≤ fuel at bound
    rw [code] at located bound
    change Riscv.Refines fuel s _ (srcCost index (src k) + c)
    rw [cost, cursorStep_src]
    by_cases hd : pos index k = 0
    · have disclosed : k.val < 36 ∧ pos index k = 0 := ⟨hk, hd⟩
      rw [if_pos disclosed, pure_bind]
      have consumed : consumedBits index (src k) = 128 := by
        rw [consumedBits_src, if_pos disclosed]
      apply readBlock_refines index payload pk 0 (by decide) k hk s cursor ctx.context ctx.regs
        ctx.atCursor ctx.aligned ctx.bounded (fun _ => ctx.room consumed) tail located bound
      · intro h
        exact absurd hd h
      · intro _ t held frame cursorReg regs located' left hleft
        apply continuation t _ (by rw [cursorStep_src, if_pos disclosed]; simp) _ located' left hleft
        refine ⟨ctx.read consumed (frameInputs_of_slot hk frame) regs cursorReg, ?_⟩
        intro k' hk' hp' notin
        dsimp only
        by_cases same : k' = k
        · rw [same, Function.update_self]
          exact src_value payload k cursor t held
        · have notin' : src k' ∉ src k :: rest := by
            simp only [List.mem_cons, not_or]
            exact ⟨fun h => same (Name.src.inj h), notin⟩
          rw [Function.update_of_ne (src_fin_ne k (src k') (fun h => same (Name.src.inj h)))]
          exact Holds.frame hk hk' same _ (src_len_le k') frame (holds k' hk' hp' notin')
    · have undisclosed : ¬ (k.val < 36 ∧ pos index k = 0) := fun h => hd h.2
      rw [if_neg undisclosed, pure_bind]
      have consumed : consumedBits index (src k) = 0 := by
        rw [consumedBits_src, if_neg undisclosed]
      apply readBlock_refines index payload pk 0 (by decide) k hk s cursor ctx.context ctx.regs
        ctx.atCursor ctx.aligned ctx.bounded (fun h => absurd h hd) tail located bound
      · intro _ t mem regs located' left hleft
        apply continuation t _ (by rw [cursorStep_src, if_neg undisclosed]; simp) _ located' left hleft
        refine ⟨ctx.skip mem regs, ?_⟩
        intro k' hk' hp' notin
        dsimp only
        have same : k' ≠ k := fun h => hd (h ▸ hp')
        have notin' : src k' ∉ src k :: rest := by
          simp only [List.mem_cons, not_or]
          exact ⟨fun h => same (Name.src.inj h), notin⟩
        rw [Function.update_of_ne (src_fin_ne k (src k') (fun h => same (Name.src.inj h)))]
        exact memBits_of_mem_eq mem (holds k' hk' hp' notin')
      · intro h
        exact absurd h hd
  · apply Segment.NodeRefines.ofPure
    · simp [srcSeg, srcCode, hk]
    · simp [srcSeg, srcCost, hk]
    · intro s x cursor rest _ inv r hr
      obtain ⟨ctx, holds⟩ := inv
      rw [cursorStep_src, if_neg (fun h => hk h.1)] at hr
      simp only [support_pure, Set.mem_singleton_iff] at hr
      subst hr
      refine ⟨ctx.drop, ?_⟩
      intro k' hk' hp' notin
      have same : k' ≠ k := fun h => hk (h ▸ hk')
      have notin' : src k' ∉ src k :: rest := by
        simp only [List.mem_cons, not_or]
        exact ⟨fun h => same (Name.src.inj h), notin⟩
      show MemBits s (slotAddr k') (Function.update x (src k).fin 0 (src k').fin)
      rw [Function.update_of_ne (src_fin_ne k (src k') (fun h => same (Name.src.inj h)))]
      exact holds k' hk' hp' notin'
    · intro x cursor
      exact ⟨_, by rw [cursorStep_src, if_neg (fun h => hk h.1)]⟩


/-! ## Chain inputs -/

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

/-- Evaluated chains hold their input for level `t`. -/
def ChainRep (s : MachineState) (x : graph.Assignment) (t : Fin 14) : Prop :=
  ∀ k : Fin 63, k.val < 36 → pos index k ≤ t.val → Holds s k (x (prev k t).fin)

/-- The tagged chain input of a processed node. -/
def Tagged (x : graph.Assignment) (k : Fin 63) (t : Fin 14) : Prop :=
  x (ci k t).fin =
    (tw (ch k t) ++ Forest.trunc (x (prev k t).fin)).cast (graph_len_fin (ci k t)).symm

def CiInv (t : Fin 14) (after : List Name) (s : MachineState) (x : graph.Assignment) (cursor : ℕ)
    (rem : List Name) : Prop :=
  ChainCtx index payload pk s cursor (rem ++ after) ∧ ChainRep index s x t ∧
  ∀ k : Fin 63, k.val < 36 → pos index k ≤ t.val → ci k t ∉ rem → Tagged x k t

def ciSeg (t : Fin 14) (after : List Name) : Segment :=
  ⟨fun _ => [], fun _ => 0, CiInv index payload pk t after⟩

theorem ci_refines (t : Fin 14) (after : List Name) (k : Fin 63) :
    (ciSeg index payload pk t after).NodeRefines index payload (ci k t) := by
  apply Segment.NodeRefines.ofPure
  · rfl
  · rfl
  · intro s x cursor rest _ inv r hr
    obtain ⟨ctx, rep, tagged⟩ := inv
    rw [cursorStep_ci] at hr
    have value : ∃ v, r = (Function.update x (ci k t).fin v, cursor) ∧
        (k.val < 36 → pos index k ≤ t.val →
          v = (tw (ch k t) ++ Forest.trunc (x (prev k t).fin)).cast (graph_len_fin (ci k t)).symm) := by
      split_ifs at hr with h
      · simp only [support_pure, Set.mem_singleton_iff] at hr
        exact ⟨_, hr, fun _ _ => rfl⟩
      · simp only [support_pure, Set.mem_singleton_iff] at hr
        exact ⟨_, hr, fun hk hp => absurd ⟨hk, hp⟩ h⟩
    obtain ⟨v, rfl, hv⟩ := value
    refine ⟨ctx.drop, ?_, ?_⟩
    · intro k' hk' hp'
      show Holds s k' (Function.update x (ci k t).fin v (prev k' t).fin)
      rw [Function.update_of_ne (fin_ne_of_ne (prev_ne_ci k k' t))]
      exact rep k' hk' hp'
    · intro k' hk' hp' notin
      unfold Tagged
      dsimp only
      rw [Function.update_of_ne (fin_ne_of_ne (prev_ne_ci k k' t))]
      by_cases same : k' = k
      · subst same
        rw [Function.update_self, hv hk' hp']
      · rw [Function.update_of_ne (fin_ne_of_ne (fun h => same (Name.ci.inj h).1))]
        have notin' : ci k' t ∉ ci k t :: rest := by
          simp only [List.mem_cons, not_or]
          exact ⟨fun h => same (Name.ci.inj h).1, notin⟩
        exact tagged k' hk' hp' notin'
  · intro x cursor
    by_cases h : k.val < 36 ∧ pos index k ≤ t.val
    · exact ⟨_, by rw [cursorStep_ci, if_pos h]⟩
    · exact ⟨_, by rw [cursorStep_ci, if_neg h]⟩

/-! ## Chain hashes -/

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

def chCode (t : Fin 14) : Name → Code
  | .ch k _ => if k.val < 36 then hashChain t.val k.val else []
  | _ => []

def chCost (t : Fin 14) : Name → ℕ
  | .ch k _ => if k.val < 36 then (if pos index k ≤ t.val then 9 else 3) else 0
  | _ => 0

theorem hashChain_length_le (t : Fin 14) (k : Fin 63) : (hashChain t k).length ≤ 9 := by
  rw [hashChain_length, hashBody_length]
  have := writeTag_le (BitVec.ofNat 16 (126 + 189 * t.val + k.val)) (chainSlot k + 16)
  omega

/-- Pending chains hold their tagged input; hashed chains hold the whole answer. -/
def ChInv (t : Fin 14) (after : List Name) (s : MachineState) (x : graph.Assignment) (cursor : ℕ)
    (rem : List Name) : Prop :=
  ChainCtx index payload pk s cursor (rem ++ after) ∧
  ∀ k : Fin 63, k.val < 36 → pos index k ≤ t.val →
    (ch k t ∈ rem → Holds s k (x (prev k t).fin) ∧ Tagged x k t) ∧
    (ch k t ∉ rem → Holds s k (x (ch k t).fin))

def chSeg (t : Fin 14) (after : List Name) : Segment :=
  ⟨chCode t, chCost index t, ChInv index payload pk t after⟩

/-- The input length is the chain input's node length. -/
theorem ci_len (k : Fin 63) (t : Fin 14) : graph.len (ci k t).fin = 144 := graph_len_fin (ci k t)

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

theorem branch_admitted (L : ℕ) (_hL : L < 1023) :
    Riscv.admittedInstruction (.BEQ .x26 .x0 (BitVec.ofNat 13 (4 * (L + 1)))) = true := by
  simp [Riscv.admittedInstruction, BitVec.toNat_ofNat]
  omega

theorem branch_ordinary (L : ℕ) :
    (Instr.BEQ .x26 .x0 (BitVec.ofNat 13 (4 * (L + 1)))) ≠ .ECALL := by
  intro h
  cases h

theorem mem_support_hash {n : ℕ} (u : BitVec n) (y : BitVec 256) :
    y ∈ support (hash paperParams u) := by
  have h : support (hash paperParams u) = Set.univ := by simp [OptimalOTS.hash]
  rw [h]
  exact Set.mem_univ y

theorem ch_refines (t : Fin 14) (after : List Name) (k : Fin 63) :
    (chSeg index payload pk t after).NodeRefines index payload (ch k t) := by
  by_cases hk : k.val < 36
  · intro s x cursor rest tail K c budget fuel fresh inv located0 bound continuation
    obtain ⟨ctx, facts⟩ := inv
    have code : chCode t (ch k t) = hashChain t k := by simp [chCode, hk]
    have cost : chCost index t (ch k t) = if pos index k ≤ t.val then 9 else 3 := by
      simp [chCost, hk]
    change Riscv.CodeAt s s.pc (chCode t (ch k t) ++ tail) at located0
    change (chCode t (ch k t)).length + budget ≤ fuel at bound
    rw [code] at located0 bound
    have located := located0
    rw [hashChain_parts, List.append_assoc] at located
    rw [hashChain_length] at bound
    change Riscv.Refines fuel s _ (chCost index t (ch k t) + c)
    rw [cost, cursorStep_ch]
    have bodyLen := hashBody_length t k
    have tagLen := writeTag_le (BitVec.ofNat 16 (126 + 189 * t.val + k.val)) (chainSlot k + 16)
    have total : (hashChain t k).length = (hashBody t k).length + 4 := by rw [hashChain_length]; omega
    -- the prefix
    obtain ⟨flag, prefixRegs, prefixMem⟩ := hashPrefix_effect s t k (by omega) k.isLt
    have prefixReady := hashPrefix_ready s t k k.isLt ctx.context.positionBase
    have prefixLength : (hashPrefix t k).length = 2 := rfl
    set u := (hashPrefix t k).foldl execInstrBr s with hu
    have uPc : u.pc = s.pc + BitVec.ofNat 64 8 := by
      rw [hu, Riscv.linear_fold_pc s _ prefixReady, prefixLength]
    have uCode : Riscv.CodeAt u u.pc (whenNonzero .x26 (hashBody t k ++ [Instr.ECALL]) ++ tail) := by
      rw [uPc, show (8 : ℕ) = 4 * (hashPrefix t k).length by rw [prefixLength]]
      exact located.append_right.code_eq (Riscv.fold_code s _)
    have uCodeEq : u.code = s.code := Riscv.fold_code s _
    have uFlag : u.getReg .x26 = if pos index k ≤ t.val then 1 else 0 := by
      rw [hu, flag, ctx.context.positions k hk,
        ult_small _ _ (by have := (fixedPositions index k).isLt; omega) (by omega)]
      simp only [decide_eq_true_eq]
      by_cases h : (fixedPositions index k).val ≤ t.val
      · rw [if_pos (show pos index k ≤ t.val from h), if_pos (by omega)]
      · rw [if_neg (show ¬ pos index k ≤ t.val from h), if_neg (by omega)]
    have bodyShort : (hashBody t k ++ [Instr.ECALL]).length < 1023 := by
      rw [List.length_append, bodyLen]; simp; omega
    have transition := whenNonzero_transition u .x26 (hashBody t k ++ [Instr.ECALL]) bodyShort
      uCode.append_left
    have fetch := uCode.append_left.head
    have skipLen : (hashBody t k ++ [Instr.ECALL]).length + 1 = (hashBody t k).length + 2 := by
      simp
    by_cases he : pos index k ≤ t.val
    · -- the chain is hashed
      rw [if_pos he]
      refine Riscv.Refines.mono (c := (hashChain t k).length + c) ?_
        (by have := hashChain_length_le t k; omega)
      rw [show fuel = (hashPrefix t k).length + ((fuel - 3) + 1) by rw [prefixLength]; omega,
        show (hashChain t k).length + c =
          (hashPrefix t k).length + (((hashBody t k).length + 1 + c) + 1) by
            rw [prefixLength, total]; omega]
      apply Riscv.Refines.linear _ located.append_left prefixReady
      rw [← hu]
      have taken : u.getReg .x26 ≠ 0 := by rw [uFlag, if_pos he]; decide
      rw [if_neg taken] at transition
      have evaluated : k.val < 36 ∧ pos index k ≤ t.val := ⟨hk, he⟩
      rw [if_pos evaluated]
      obtain ⟨held, tagged⟩ := (facts k hk he).1 (by simp)
      set n := u.setPC (u.pc + 4) with hn
      have nCode : Riscv.CodeAt n n.pc (hashBody t k ++ ([Instr.ECALL] ++ tail)) := by
        have h : Riscv.CodeAt u (u.pc + 4) (hashBody t k ++ ([Instr.ECALL] ++ tail)) := by
          simpa only [List.append_eq, List.append_assoc] using uCode.tail
        exact h.code_eq rfl
      have nRegs : ∀ r, r ≠ .x26 → n.getReg r = s.getReg r := by
        intro r h26
        rw [hn, MachineState.getReg_setPC, prefixRegs r h26]
      have nMem : n.mem = s.mem := prefixMem
      have nBase : n.getReg .x18 = BitVec.ofNat 64 chainsBase := by
        rw [nRegs .x18 (by decide)]; exact ctx.regs.base
      have bodyReady := hashBody_ready n t k hk nBase
      obtain ⟨w10, w12, wRegs, wMem⟩ := hashBody_effect n t k hk
      set w := (hashBody t k).foldl execInstrBr n with hw
      have wPc : w.pc = n.pc + BitVec.ofNat 64 (4 * (hashBody t k).length) :=
        Riscv.linear_fold_pc n _ bodyReady
      have wCode : Riscv.CodeAt w w.pc ([Instr.ECALL] ++ tail) := by
        rw [wPc]
        exact nCode.append_right.code_eq (Riscv.fold_code n _)
      have wCodeEq : w.code = s.code := (Riscv.fold_code n _).trans uCodeEq
      have wFetch : w.code w.pc = some .ECALL := wCode.head
      have wCall : w.getReg .x5 = Riscv.hashCall := by
        rw [wRegs .x5 (by decide) (by decide) (by decide), nRegs .x5 (by decide)]
        exact ctx.regs.call
      have wLen : w.getReg .x11 = 144 := by
        rw [wRegs .x11 (by decide) (by decide) (by decide), nRegs .x11 (by decide)]
        exact ctx.regs.length
      have wSlot : w.getReg .x10 = slotAddr k := by rw [w10, nBase]; rfl
      have wSlot' : w.getReg .x12 = slotAddr k := by rw [w12, nBase]; rfl
      have range : isValidOutputRange (slotAddr k) (((144 : Word).toNat + 7) / 8) = true := by
        show isValidOutputRange (slotAddr k) 18 = true
        exact chain_output_range ⟨k, hk⟩
      have wValid : Riscv.hashArgumentsValid w = true := by
        simp only [Riscv.hashArgumentsValid, wSlot, wSlot', wLen, Bool.and_eq_true]
        exact ⟨⟨⟨⟨range, slotAddr_access0 k hk⟩, slotAddr_access8 k hk⟩, slotAddr_access16 k hk⟩,
          slotAddr_access24 k hk⟩
      -- the query is the specification's chain input
      have heldN : MemBits n (n.getReg .x18 + BitVec.ofNat 64 (chainSlot k))
          (Forest.trunc (x (prev k t).fin)) := by
        rw [nBase]
        exact memBits_of_mem_eq nMem held.trunc
      have appended := tag_append n (chainSlot k) (Forest.trunc (x (prev k t).fin)) (tw (ch k t))
        (by decide) (by decide) (Direct.nodeTag_literal (ch k t)) (by unfold chainSlot; omega)
        (by unfold chainSlot; omega) (by rw [nBase]; decide) (by rw [nBase]; decide) heldN
      have tagEq : tw (ch k t) = BitVec.ofNat 16 (126 + 189 * t.val + k.val) := rfl
      have wMem' : w.mem = ((Direct.writeTag (tw (ch k t)) (chainSlot k + 128 / 8)).foldl execInstrBr n).mem := by
        rw [wMem, tagEq, Direct.writeTag_memory n _ _ (by unfold chainSlot; omega)
          (chainTag_literal t k)]
      have wInput : Riscv.hashInput w = ⟨graph.len (ci k t).fin, x (ci k t).fin⟩ := by
        apply hashInput_of_memBits wSlot
        · rw [wLen, ci_len]; rfl
        · rw [tagged]
          apply (Direct.memBits_cast _ _ _ _).mpr
          have h := memBits_of_mem_eq wMem' appended
          rw [nBase] at h
          exact h
      have blocks : blockCost paperParams (graph.len (ci k t).fin) = 1 := by
        rw [ci_len]; decide
      -- compose: branch, body, hash, continuation
      rw [show (hashBody t k).length + 1 + c + 1 = ((hashBody t k).length + (1 + c)) + 1 by omega]
      apply Riscv.Refines.branch fetch (branch_admitted _ bodyShort) (branch_ordinary _) transition
      rw [show fuel - 3 = (hashBody t k).length + ((fuel - 3 - (hashBody t k).length - 1) + 1) by omega]
      apply Riscv.Refines.linear _ nCode.append_left bodyReady
      rw [← hw]
      simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp_apply, pure_bind]
      have step := Riscv.Refines.hash (fuel := fuel - 3 - (hashBody t k).length - 1) wFetch wCall wValid
        (k := fun y => K (Function.update x (ch k t).fin (y.cast (graph_len_fin (ch k t)).symm), cursor))
        (c := c) ?_
      · rw [wInput, blocks] at step
        exact step
      intro y
      -- the state after the answer is written
      set v := Riscv.writeHash w y with hv
      have vRegs : ∀ r, r ≠ .x10 → r ≠ .x12 → r ≠ .x26 → v.getReg r = s.getReg r := by
        intro r h10 h12 h26
        rw [hv, writeHash_regs, wRegs r h10 h12 h26, nRegs r h26]
      have slotFrame : ∀ addr, (∀ j, j < 4 → addr ≠ slotAddr k + BitVec.ofNat 64 (8 * j)) →
          v.getMem addr = s.getMem addr := by
        intro addr outside
        rw [hv, writeHash_frame _ _ _ (by rw [wSlot']; exact outside)]
        have hw' : w.getMem addr = (n.setHalfword (n.getReg .x18 + BitVec.ofNat 64 (chainSlot k + 16))
            (BitVec.ofNat 16 (126 + 189 * t.val + k.val))).getMem addr := by
          simp only [MachineState.getMem, wMem]
        rw [hw', MachineState.setHalfword]
        have tagWord : alignToDword (n.getReg .x18 + BitVec.ofNat 64 (chainSlot k + 16)) =
            slotAddr k + BitVec.ofNat 64 (8 * 2) := by
          rw [nBase, slotAddr_word, show chainSlot k + 8 * 2 = chainSlot k + 16 by omega]
          exact aligned_offset _ (by decide) _ (by unfold chainSlot; omega)
            (by simp only [BitVec.toNat_ofNat, chainsBase, chainSlot]; omega)
        rw [MachineState.getMem_setMem_ne (by rw [tagWord]; exact outside 2 (by decide))]
        simp only [MachineState.getMem, nMem]
      have vPc : v.pc = s.pc + BitVec.ofNat 64 (4 * (hashChain t k).length) := by
        rw [hv, writeHash_pc, wPc, hn, MachineState.setPC, uPc, total]
        simp only
        rw [show (4 : Word) = BitVec.ofNat 64 4 from rfl, pcAdd, pcAdd, pcAdd]
        congr 1
        congr 1
        omega
      have vCode : v.code = s.code := by rw [hv, writeHash_code, wCodeEq]
      have vLocated : Riscv.CodeAt v v.pc tail := by
        rw [vPc]
        exact located0.append_right.code_eq vCode
      have answer : Holds v k ((y.cast (graph_len_fin (ch k t)).symm : BitVec (graph.len (ch k t).fin))) := by
        unfold Holds
        apply (Direct.memBits_cast _ _ _ _).mpr
        have h := writeHash_memBits w y (by rw [wSlot']; exact slotAddr_aligned k hk)
        rw [wSlot'] at h
        exact h
      apply continuation v
        (Function.update x (ch k t).fin (y.cast (graph_len_fin (ch k t)).symm), cursor) ?_ ?_
        vLocated (fuel - 3 - (hashBody t k).length - 1) (by omega)
      · rw [cursorStep_ch, if_pos evaluated, support_map]
        exact ⟨y, mem_support_hash _ y, rfl⟩
      · refine ⟨ctx.hashed (frameInputs_of_slot hk slotFrame) vRegs, ?_⟩
        intro k' hk' hp'
        dsimp only
        by_cases same : k' = k
        · subst same
          refine ⟨fun h => absurd h fresh, fun _ => ?_⟩
          rw [Function.update_self]
          exact answer
        · have neCh : (ch k' t).fin ≠ (ch k t).fin :=
            fin_ne_of_ne (fun h => same (Name.ch.inj h).1)
          have nePrev : (prev k' t).fin ≠ (ch k t).fin := fin_ne_of_ne (prev_ne_ch k k' t)
          have neCi : (ci k' t).fin ≠ (ch k t).fin := fin_ne_of_ne (by simp)
          refine ⟨fun hmem => ?_, fun hnot => ?_⟩
          · obtain ⟨held', tagged'⟩ := (facts k' hk' hp').1 (by simp [hmem])
            refine ⟨?_, ?_⟩
            · rw [Function.update_of_ne nePrev]
              exact Holds.frame hk hk' same _ (prev_len_le k' t) slotFrame held'
            · unfold Tagged
              rw [Function.update_of_ne neCi, Function.update_of_ne nePrev]
              exact tagged'
          · have hnot' : ch k' t ∉ ch k t :: rest := by
              simp only [List.mem_cons, not_or]
              exact ⟨fun h => same (Name.ch.inj h).1, hnot⟩
            rw [Function.update_of_ne neCh]
            exact Holds.frame hk hk' same _ (ch_len_le k' t) slotFrame ((facts k' hk' hp').2 hnot')
    · -- the chain is skipped
      rw [if_neg he]
      rw [show fuel = (hashPrefix t k).length + ((fuel - 3) + 1) by rw [prefixLength]; omega,
        show 3 + c = (hashPrefix t k).length + (c + 1) by rw [prefixLength]; omega]
      apply Riscv.Refines.linear _ located.append_left prefixReady
      rw [← hu]
      have zero : u.getReg .x26 = 0 := by rw [uFlag, if_neg he]
      rw [if_pos zero] at transition
      have unevaluated : ¬ (k.val < 36 ∧ pos index k ≤ t.val) := fun h => he h.2
      rw [if_neg unevaluated, pure_bind]
      set n := u.setPC (u.pc + BitVec.ofNat 64 (4 * ((hashBody t k ++ [Instr.ECALL]).length + 1)))
        with hn
      have nRegs : ∀ r, r ≠ .x26 → r ≠ .x27 → n.getReg r = s.getReg r := by
        intro r h26 _
        rw [hn, MachineState.getReg_setPC, prefixRegs r h26]
      have nMem : n.mem = s.mem := prefixMem
      have nPc : n.pc = s.pc + BitVec.ofNat 64 (4 * (hashChain t k).length) := by
        rw [hn, MachineState.setPC, uPc, skipLen, total]
        simp only
        rw [pcAdd]
        congr 1
        congr 1
        omega
      have nLocated : Riscv.CodeAt n n.pc tail := by
        rw [nPc]
        exact located0.append_right.code_eq uCodeEq
      have skipped : Riscv.Refines (fuel - 3) n (K (Function.update x (ch k t).fin 0, cursor)) c := by
        apply continuation n (Function.update x (ch k t).fin 0, cursor)
          (by rw [cursorStep_ch, if_neg unevaluated]; simp) ?_ nLocated (fuel - 3) (by omega)
        refine ⟨ctx.skip nMem nRegs, ?_⟩
        intro k' hk' hp'
        dsimp only
        have same : k' ≠ k := fun h => he (h ▸ hp')
        have neCh : (ch k' t).fin ≠ (ch k t).fin := fin_ne_of_ne (fun h => same (Name.ch.inj h).1)
        have nePrev : (prev k' t).fin ≠ (ch k t).fin := fin_ne_of_ne (prev_ne_ch k k' t)
        have neCi : (ci k' t).fin ≠ (ch k t).fin := fin_ne_of_ne (by simp)
        refine ⟨fun hmem => ?_, fun hnot => ?_⟩
        · obtain ⟨held', tagged'⟩ := (facts k' hk' hp').1 (by simp [hmem])
          refine ⟨?_, ?_⟩
          · rw [Function.update_of_ne nePrev]
            exact memBits_of_mem_eq nMem held'
          · unfold Tagged
            rw [Function.update_of_ne neCi, Function.update_of_ne nePrev]
            exact tagged'
        · have hnot' : ch k' t ∉ ch k t :: rest := by
            simp only [List.mem_cons, not_or]
            exact ⟨fun h => same (Name.ch.inj h).1, hnot⟩
          rw [Function.update_of_ne neCh]
          exact memBits_of_mem_eq nMem ((facts k' hk' hp').2 hnot')
      exact Riscv.Refines.branch fetch (branch_admitted _ bodyShort) (branch_ordinary _) transition
        skipped
  · apply Segment.NodeRefines.ofPure
    · simp [chSeg, chCode, hk]
    · simp [chSeg, chCost, hk]
    · intro s x cursor rest _ inv r hr
      obtain ⟨ctx, facts⟩ := inv
      rw [cursorStep_ch, if_neg (fun h => hk h.1)] at hr
      simp only [support_pure, Set.mem_singleton_iff] at hr
      subst hr
      refine ⟨ctx.drop, ?_⟩
      intro k' hk' hp'
      dsimp only
      have same : k' ≠ k := fun h => hk (h ▸ hk')
      have neCh : (ch k' t).fin ≠ (ch k t).fin := fin_ne_of_ne (fun h => same (Name.ch.inj h).1)
      have nePrev : (prev k' t).fin ≠ (ch k t).fin := fin_ne_of_ne (prev_ne_ch k k' t)
      have neCi : (ci k' t).fin ≠ (ch k t).fin := fin_ne_of_ne (by simp)
      refine ⟨fun hmem => ?_, fun hnot => ?_⟩
      · obtain ⟨held', tagged'⟩ := (facts k' hk' hp').1 (by simp [hmem])
        refine ⟨?_, ?_⟩
        · rw [Function.update_of_ne nePrev]; exact held'
        · unfold Tagged
          rw [Function.update_of_ne neCi, Function.update_of_ne nePrev]
          exact tagged'
      · have hnot' : ch k' t ∉ ch k t :: rest := by
          simp only [List.mem_cons, not_or]
          exact ⟨fun h => same (Name.ch.inj h).1, hnot⟩
        rw [Function.update_of_ne neCh]
        exact (facts k' hk' hp').2 hnot'
    · intro x cursor
      exact ⟨_, by rw [cursorStep_ch, if_neg (fun h => hk h.1)]⟩


/-! ## Chain values -/

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

theorem consumedBits_cv (k : Fin 63) (t : Fin 14) :
    consumedBits index (cv k t) = if k.val < 36 ∧ pos index k = t.val + 1 then 128 else 0 := by
  rw [consumedBits_word, disclosed_cv]
  by_cases h : k.val < 36 ∧ pos index k = t.val + 1 <;> simp [h]

def cvCode (t : Fin 14) : Name → Code
  | .cv k _ => if k.val < 36 then readChain (t.val + 1) k.val else []
  | _ => []

def cvCost (t : Fin 14) : Name → ℕ
  | .cv k _ => if k.val < 36 then readCost index (t.val + 1) k else 0
  | _ => 0

/-- Evaluated chains hold their answers and, once visited, their values are the truncations;
chains disclosed at this level hold their words once read. -/
def CvInv (t : Fin 14) (after : List Name) (s : MachineState) (x : graph.Assignment) (cursor : ℕ)
    (rem : List Name) : Prop :=
  ChainCtx index payload pk s cursor (rem ++ after) ∧
  ∀ k : Fin 63, k.val < 36 →
    (pos index k ≤ t.val → Holds s k (x (ch k t).fin)) ∧
    (pos index k ≤ t.val → cv k t ∉ rem →
      x (cv k t).fin = (Forest.trunc (x (ch k t).fin)).cast (graph_len_fin (cv k t)).symm) ∧
    (pos index k = t.val + 1 → cv k t ∉ rem → Holds s k (x (cv k t).fin))

def cvSeg (t : Fin 14) (after : List Name) : Segment :=
  ⟨cvCode t, cvCost index t, CvInv index payload pk t after⟩

theorem cv_value (k : Fin 63) (t : Fin 14) (cursor : ℕ) (u : MachineState)
    (held : MemBits u (slotAddr k) (ofBits 128 (payload.drop cursor))) :
    Holds u k (ofBits (graph.len (cv k t).fin) ((payload.drop cursor).take (graph.len (cv k t).fin))) := by
  have length : graph.len (cv k t).fin = 128 := graph_len_fin (cv k t)
  unfold Holds
  rw [length]
  have take : ofBits 128 ((payload.drop cursor).take 128) = ofBits 128 (payload.drop cursor) := by
    simpa only [List.drop_zero] using
      ofBits_drop_take (payload.drop cursor) (cap := 128) (start := 0) (len := 128) (by decide)
  rw [take]
  exact held

theorem ch_ne_cv (k k' : Fin 63) (t : Fin 14) : ch k' t ≠ cv k t := by simp

theorem cv_refines (t : Fin 14) (after : List Name) (k : Fin 63) :
    (cvSeg index payload pk t after).NodeRefines index payload (cv k t) := by
  have ht : t.val + 1 < 15 := by omega
  by_cases hk : k.val < 36
  · intro s x cursor rest tail K c budget fuel _ inv located bound continuation
    obtain ⟨ctx, facts⟩ := inv
    have code : cvCode t (cv k t) = readChain (t.val + 1) k := by simp [cvCode, hk]
    have cost : cvCost index t (cv k t) = readCost index (t.val + 1) k := by simp [cvCost, hk]
    change Riscv.CodeAt s s.pc (cvCode t (cv k t) ++ tail) at located
    change (cvCode t (cv k t)).length + budget ≤ fuel at bound
    rw [code] at located bound
    change Riscv.Refines fuel s _ (cvCost index t (cv k t) + c)
    rw [cost, cursorStep_cv]
    by_cases hd : pos index k = t.val + 1
    · have disclosed : k.val < 36 ∧ pos index k = t.val + 1 := ⟨hk, hd⟩
      rw [if_pos disclosed, pure_bind]
      have consumed : consumedBits index (cv k t) = 128 := by
        rw [consumedBits_cv, if_pos disclosed]
      apply readBlock_refines index payload pk (t.val + 1) ht k hk s cursor ctx.context ctx.regs
        ctx.atCursor ctx.aligned ctx.bounded (fun _ => ctx.room consumed) tail located bound
      · intro h
        exact absurd hd h
      · intro _ u held frame cursorReg regs located' left hleft
        apply continuation u _ (by rw [cursorStep_cv, if_pos disclosed]; simp) _ located' left hleft
        refine ⟨ctx.read consumed (frameInputs_of_slot hk frame) regs cursorReg, ?_⟩
        intro k' hk'
        dsimp only
        by_cases same : k' = k
        · rw [same]
          refine ⟨fun hp => absurd hp (by omega), fun hp => absurd hp (by omega), fun _ _ => ?_⟩
          rw [Function.update_self]
          exact cv_value payload k t cursor u held
        · have neCv : (cv k' t).fin ≠ (cv k t).fin := fin_ne_of_ne (fun h => same (Name.cv.inj h).1)
          have neCh : (ch k' t).fin ≠ (cv k t).fin := fin_ne_of_ne (ch_ne_cv k k' t)
          have notin : ∀ hn : cv k' t ∉ rest, cv k' t ∉ cv k t :: rest := fun hn => by
            simp only [List.mem_cons, not_or]
            exact ⟨fun h => same (Name.cv.inj h).1, hn⟩
          obtain ⟨h1, h2, h3⟩ := facts k' hk'
          refine ⟨fun hp => ?_, fun hp hn => ?_, fun hp hn => ?_⟩
          · rw [Function.update_of_ne neCh]
            exact Holds.frame hk hk' same _ (ch_len_le k' t) frame (h1 hp)
          · rw [Function.update_of_ne neCv, Function.update_of_ne neCh]
            exact h2 hp (notin hn)
          · rw [Function.update_of_ne neCv]
            exact Holds.frame hk hk' same _ (cv_len_le k' t) frame (h3 hp (notin hn))
    · have undisclosed : ¬ (k.val < 36 ∧ pos index k = t.val + 1) := fun h => hd h.2
      rw [if_neg undisclosed]
      have step : ∃ v : BitVec (graph.len (cv k t).fin),
          (if k.val < 36 ∧ pos index k ≤ t.val then
            (pure (Function.update x (cv k t).fin
              ((Forest.trunc (x (ch k t).fin)).cast (graph_len_fin (cv k t)).symm), cursor) :
              OracleComp (Spec paperParams) (graph.Assignment × ℕ))
          else pure (Function.update x (cv k t).fin 0, cursor)) =
            pure (Function.update x (cv k t).fin v, cursor) ∧
          (pos index k ≤ t.val →
            v = (Forest.trunc (x (ch k t).fin)).cast (graph_len_fin (cv k t)).symm) := by
        split_ifs with h
        · exact ⟨_, rfl, fun _ => rfl⟩
        · exact ⟨_, rfl, fun hp => absurd ⟨hk, hp⟩ h⟩
      obtain ⟨v, hv, hval⟩ := step
      rw [hv, pure_bind]
      apply readBlock_refines index payload pk (t.val + 1) ht k hk s cursor ctx.context ctx.regs
        ctx.atCursor ctx.aligned ctx.bounded (fun h => absurd h hd) tail located bound
      · intro _ u mem regs located' left hleft
        apply continuation u (Function.update x (cv k t).fin v, cursor)
          (by rw [cursorStep_cv, if_neg undisclosed, hv]; simp) ?_ located' left hleft
        refine ⟨ctx.skip mem regs, ?_⟩
        intro k' hk'
        dsimp only
        have neCh' : (ch k t).fin ≠ (cv k t).fin := fin_ne_of_ne (ch_ne_cv k k t)
        by_cases same : k' = k
        · rw [same]
          obtain ⟨h1, h2, h3⟩ := facts k hk
          refine ⟨fun hp => ?_, fun hp _ => ?_, fun hp => absurd hp hd⟩
          · rw [Function.update_of_ne neCh']
            exact memBits_of_mem_eq mem (h1 hp)
          · rw [Function.update_self, Function.update_of_ne neCh']
            exact hval hp
        · have neCv : (cv k' t).fin ≠ (cv k t).fin := fin_ne_of_ne (fun h => same (Name.cv.inj h).1)
          have neCh : (ch k' t).fin ≠ (cv k t).fin := fin_ne_of_ne (ch_ne_cv k k' t)
          have notin : ∀ hn : cv k' t ∉ rest, cv k' t ∉ cv k t :: rest := fun hn => by
            simp only [List.mem_cons, not_or]
            exact ⟨fun h => same (Name.cv.inj h).1, hn⟩
          obtain ⟨h1, h2, h3⟩ := facts k' hk'
          refine ⟨fun hp => ?_, fun hp hn => ?_, fun hp hn => ?_⟩
          · rw [Function.update_of_ne neCh]
            exact memBits_of_mem_eq mem (h1 hp)
          · rw [Function.update_of_ne neCv, Function.update_of_ne neCh]
            exact h2 hp (notin hn)
          · rw [Function.update_of_ne neCv]
            exact memBits_of_mem_eq mem (h3 hp (notin hn))
      · intro h
        exact absurd h hd
  · apply Segment.NodeRefines.ofPure
    · simp [cvSeg, cvCode, hk]
    · simp [cvSeg, cvCost, hk]
    · intro s x cursor rest _ inv r hr
      obtain ⟨ctx, facts⟩ := inv
      rw [cursorStep_cv, if_neg (fun h => hk h.1), if_neg (fun h => hk h.1)] at hr
      simp only [support_pure, Set.mem_singleton_iff] at hr
      subst hr
      refine ⟨ctx.drop, ?_⟩
      intro k' hk'
      dsimp only
      have same : k' ≠ k := fun h => hk (h ▸ hk')
      have neCv : (cv k' t).fin ≠ (cv k t).fin := fin_ne_of_ne (fun h => same (Name.cv.inj h).1)
      have neCh : (ch k' t).fin ≠ (cv k t).fin := fin_ne_of_ne (ch_ne_cv k k' t)
      have notin : ∀ hn : cv k' t ∉ rest, cv k' t ∉ cv k t :: rest := fun hn => by
        simp only [List.mem_cons, not_or]
        exact ⟨fun h => same (Name.cv.inj h).1, hn⟩
      obtain ⟨h1, h2, h3⟩ := facts k' hk'
      refine ⟨fun hp => ?_, fun hp hn => ?_, fun hp hn => ?_⟩
      · rw [Function.update_of_ne neCh]; exact h1 hp
      · rw [Function.update_of_ne neCv, Function.update_of_ne neCh]; exact h2 hp (notin hn)
      · rw [Function.update_of_ne neCv]; exact h3 hp (notin hn)
    · intro x cursor
      exact ⟨_, by rw [cursorStep_cv, if_neg (fun h => hk h.1), if_neg (fun h => hk h.1)]⟩

end OptimalOTS.RiscvUpperProgram.Compact
