import Submissions.RiscvUpper.NodeProgramProof

/-! Memory effects of the direct forest's deterministic operations. -/

set_option maxRecDepth 4000
set_option maxHeartbeats 1000000

namespace OptimalOTS.RiscvUpperProgram.Direct

open RiscvZkvm.Rv64 Forest Forest.Name RiscvUpperForest.ForestVerifier OracleComp

set_option allowUnsafeReducibility true
attribute [local reducible] Forest.graph

/-- Copying a child changes only the copy macro's address and value temporaries. -/
theorem copyChild_register (s : MachineState) (child : Name) (off : ℕ) (r : Reg)
    (h7 : r ≠ .x7) (h26 : r ≠ .x26) (h27 : r ≠ .x27) :
    ((copyChild child off).foldl execInstrBr s).getReg r = s.getReg r := by
  rw [copyChild, List.foldl_append, copy128_reg _ _ _ _ _ _ h26 h27]
  exact constant_preserves _ _ _ _ h7.symm

/-- The only words changed by a child copy are its two destination words. -/
theorem copyChild_frame (s : MachineState) (child : Name) (off : ℕ) (addr : Word)
    (small : off + 8 < 2048)
    (first : addr ≠ s.getReg .x18 + BitVec.ofNat 64 off)
    (second : addr ≠ s.getReg .x18 + BitVec.ofNat 64 (off + 8)) :
    ((copyChild child off).foldl execInstrBr s).getMem addr = s.getMem addr := by
  rw [copyChild, List.foldl_append, copy128_getMem _ _ _ _ _ (by decide) (by decide) (by decide)]
  simp only [constant_preserves _ .x7 .x18 _ (by decide),
    signExtend12_nonnegative _ small, signExtend12_nonnegative _ (by omega : off < 2048),
    if_neg first, if_neg second]
  exact congrFun (constant_mem s .x7 (slotAddress child)) addr

/-- A copied value cannot disturb any other node's slot. -/
theorem copyChild_other {width : ℕ} (s : MachineState) (dest child other : Name)
    (j : ℕ) (hj : j + 1 < 16) (value : BitVec width) (small : width ≤ 1024)
    (different : dest ≠ other) (destination : s.getReg .x18 = BitVec.ofNat 64 (slotAddress dest))
    (represented : MemBits s (BitVec.ofNat 64 (slotAddress other)) value) :
    MemBits ((copyChild child (8 * j)).foldl execInstrBr s)
      (BitVec.ofNat 64 (slotAddress other)) value := by
  apply memBits_of_word_frame s _ _ value represented
  intro i hi
  apply copyChild_frame _ _ _ _ (by omega)
  · rw [destination, slot_bit_word other i (by omega)]
    exact slot_word_ne other dest (i / 64) j (by omega) (by omega) different.symm
  · rw [destination, slot_bit_word other i (by omega), show 8 * j + 8 = 8 * (j + 1) by omega]
    exact slot_word_ne other dest (i / 64) (j + 1) (by omega) hj different.symm

/-- A tag store preserves all registers except its literal temporary. -/
theorem writeTag_register (s : MachineState) (tag : BitVec 16) (off : ℕ) (r : Reg)
    (different : r ≠ .x26) :
    ((writeTag tag off).foldl execInstrBr s).getReg r = s.getReg r := by
  rw [writeTag, List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil, execInstrBr, MachineState.getReg_setPC,
    MachineState.setHalfword, getReg_store]
  exact constant_preserves _ _ _ _ different.symm

set_option maxRecDepth 100000 in
/-- Tag materialization is exact for every node of this forest. -/
theorem nodeTag_literal (n : Name) :
    (literalValue (tw n).toNat).truncate 16 = tw n := by
  have checked : ∀ v : Fin N,
      (literalValue (tw (ofFin v)).toNat).truncate 16 = tw (ofFin v) := by decide +kernel
  simpa only [ofFin_fin] using checked n.fin

/-- The tag macro's exact memory update is one little-endian halfword. -/
theorem writeTag_memory (s : MachineState) (tag : BitVec 16) (off : ℕ)
    (small : off < 2048) (literal : (literalValue tag.toNat).truncate 16 = tag) :
    ((writeTag tag off).foldl execInstrBr s).mem =
      (s.setHalfword (s.getReg .x18 + BitVec.ofNat 64 off) tag).mem := by
  simp only [writeTag, List.foldl_append, List.foldl_cons, List.foldl_nil, execInstrBr,
    MachineState.setPC, constant_value _ .x26 _ (by decide),
    constant_preserves _ .x26 .x18 _ (by decide), signExtend12_nonnegative _ small, literal]
  simp only [MachineState.setHalfword, MachineState.setMem, MachineState.getMem,
    constant_mem]

/-- A tag store represents exactly the sixteen tag bits at its byte address. -/
theorem writeTag_memBits (s : MachineState) (tag : BitVec 16) (off : ℕ)
    (small : off < 2048) (literal : (literalValue tag.toNat).truncate 16 = tag)
    (aligned : alignToDword (s.getReg .x18 + BitVec.ofNat 64 off) =
      s.getReg .x18 + BitVec.ofNat 64 off) :
    MemBits ((writeTag tag off).foldl execInstrBr s)
      (s.getReg .x18 + BitVec.ofNat 64 off) tag :=
  memBits_of_mem_eq (writeTag_memory s tag off small literal)
    (memBits_setHalfword s _ tag aligned)

/-- A tag store preserves all memory words except its containing doubleword. -/
theorem writeTag_frame (s : MachineState) (tag : BitVec 16) (off : ℕ) (addr : Word)
    (small : off < 2048) (literal : (literalValue tag.toNat).truncate 16 = tag)
    (different : addr ≠ alignToDword (s.getReg .x18 + BitVec.ofNat 64 off)) :
    ((writeTag tag off).foldl execInstrBr s).getMem addr = s.getMem addr := by
  have h := congrFun (writeTag_memory s tag off small literal) addr
  change ((writeTag tag off).foldl execInstrBr s).getMem addr =
    (s.setHalfword _ _).getMem addr at h
  rw [h, MachineState.setHalfword]
  exact MachineState.getMem_setMem_ne different

/-- Word-aligned offsets retain the slot's alignment. -/
theorem slot_offset_aligned (n : Name) (off : ℕ) (aligned : off % 8 = 0) :
    alignToDword (BitVec.ofNat 64 (slotAddress n) + BitVec.ofNat 64 off) =
      BitVec.ofNat 64 (slotAddress n) + BitVec.ofNat 64 off := by
  apply (aligned_iff _).mpr
  have ha := slotAddress_aligned n
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- Copying after a complete word prefix preserves that prefix. -/
theorem copyChild_prefix {width : ℕ} (s : MachineState) (dest child : Name)
    (value : BitVec width) (bounded : width ≤ 896) (wordAligned : width % 64 = 0)
    (destination : s.getReg .x18 = BitVec.ofNat 64 (slotAddress dest))
    (represented : MemBits s (BitVec.ofNat 64 (slotAddress dest)) value) :
    MemBits ((copyChild child (width / 8)).foldl execInstrBr s)
      (BitVec.ofNat 64 (slotAddress dest)) value := by
  apply memBits_of_word_frame s _ _ value represented
  intro i hi
  apply copyChild_frame _ _ _ _ (by omega)
  · rw [destination, slot_bit_word dest i (by omega)]
    exact add_offset_ne _ (by omega) (by omega) (by omega)
  · rw [destination, slot_bit_word dest i (by omega)]
    exact add_offset_ne _ (by omega) (by omega) (by omega)

/-- Appending a child in memory implements bit-vector concatenation. -/
theorem copyChild_append {width : ℕ} (s : MachineState) (dest child : Name)
    (lo : BitVec width) (hi : BitVec 128) (bounded : width ≤ 896) (wordAligned : width % 64 = 0)
    (destination : s.getReg .x18 = BitVec.ofNat 64 (slotAddress dest))
    (preceding : MemBits s (BitVec.ofNat 64 (slotAddress dest)) lo)
    (source : MemBits s (BitVec.ofNat 64 (slotAddress child)) hi) :
    MemBits ((copyChild child (width / 8)).foldl execInstrBr s)
      (BitVec.ofNat 64 (slotAddress dest)) (hi ++ lo) := by
  apply memBits_append (by omega)
  · exact copyChild_prefix s dest child lo bounded wordAligned destination preceding
  · have copied := copyChild_memBits s child (width / 8) hi source
      (by rw [destination]; exact slot_offset_aligned dest _ (by omega)) (by omega)
    simpa only [destination] using copied

/-- The tag after a complete word prefix leaves that prefix unchanged. -/
theorem writeTag_prefix {width : ℕ} (s : MachineState) (dest : Name)
    (value : BitVec width) (tag : BitVec 16) (bounded : width ≤ 896)
    (wordAligned : width % 64 = 0) (literal : (literalValue tag.toNat).truncate 16 = tag)
    (destination : s.getReg .x18 = BitVec.ofNat 64 (slotAddress dest))
    (represented : MemBits s (BitVec.ofNat 64 (slotAddress dest)) value) :
    MemBits ((writeTag tag (width / 8)).foldl execInstrBr s)
      (BitVec.ofNat 64 (slotAddress dest)) value := by
  apply memBits_of_word_frame s _ _ value represented
  intro i hi
  apply writeTag_frame _ _ _ _ (by omega) literal
  rw [destination, slot_offset_aligned dest (width / 8) (by omega),
    slot_bit_word dest i (by omega)]
  exact add_offset_ne _ (by omega) (by omega) (by omega)

/-- Appending the sixteen-bit tag supplies the exact high bits of the hash input. -/
theorem writeTag_append {width : ℕ} (s : MachineState) (dest : Name)
    (value : BitVec width) (tag : BitVec 16) (bounded : width ≤ 896)
    (wordAligned : width % 64 = 0) (literal : (literalValue tag.toNat).truncate 16 = tag)
    (destination : s.getReg .x18 = BitVec.ofNat 64 (slotAddress dest))
    (represented : MemBits s (BitVec.ofNat 64 (slotAddress dest)) value) :
    MemBits ((writeTag tag (width / 8)).foldl execInstrBr s)
      (BitVec.ofNat 64 (slotAddress dest)) (tag ++ value) := by
  apply memBits_append (by omega)
  · exact writeTag_prefix s dest value tag bounded wordAligned literal destination represented
  · have stored := writeTag_memBits s tag (width / 8) (by omega) literal
      (by rw [destination]; exact slot_offset_aligned dest _ (by omega))
    simpa only [destination] using stored

/-- All machine memory outside a destination slot is unchanged. -/
def SlotFrame (s t : MachineState) (dest : Name) : Prop :=
  ∀ addr, (∀ j, j < 16 → addr ≠ BitVec.ofNat 64 (slotAddress dest) + BitVec.ofNat 64 (8 * j)) →
    t.getMem addr = s.getMem addr

theorem SlotFrame.refl (s : MachineState) (dest : Name) : SlotFrame s s dest :=
  fun _ _ => rfl

theorem SlotFrame.trans {s t u : MachineState} {dest : Name}
    (first : SlotFrame s t dest) (second : SlotFrame t u dest) : SlotFrame s u dest :=
  fun addr h => (second addr h).trans (first addr h)

theorem copyChild_slotFrame (s : MachineState) (dest child : Name) (j : ℕ)
    (bounded : j + 1 < 16) (destination : s.getReg .x18 = BitVec.ofNat 64 (slotAddress dest)) :
    SlotFrame s ((copyChild child (8 * j)).foldl execInstrBr s) dest := by
  intro addr h
  apply copyChild_frame _ _ _ _ (by omega)
  · rw [destination]
    exact h j (by omega)
  · rw [destination, show 8 * j + 8 = 8 * (j + 1) by omega]
    exact h (j + 1) bounded

theorem writeTag_slotFrame (s : MachineState) (dest : Name) (tag : BitVec 16) (j : ℕ)
    (bounded : j < 16) (literal : (literalValue tag.toNat).truncate 16 = tag)
    (destination : s.getReg .x18 = BitVec.ofNat 64 (slotAddress dest)) :
    SlotFrame s ((writeTag tag (8 * j)).foldl execInstrBr s) dest := by
  intro addr h
  apply writeTag_frame _ _ _ _ (by omega) literal
  rw [destination, slot_offset_aligned dest _ (by omega)]
  exact h j bounded

/-- Slot isolation transports every other represented graph value. -/
theorem SlotFrame.other {s t : MachineState} {dest other : Name}
    (frame : SlotFrame s t dest) (different : dest ≠ other)
    {width : ℕ} (value : BitVec width) (bounded : width ≤ 1024)
    (represented : MemBits s (BitVec.ofNat 64 (slotAddress other)) value) :
    MemBits t (BitVec.ofNat 64 (slotAddress other)) value := by
  apply memBits_of_word_frame s t _ value represented
  intro i hi
  apply frame
  intro j hj
  rw [slot_bit_word other i (by omega)]
  exact slot_word_ne other dest (i / 64) j (by omega) hj different.symm

/-- Earlier node values remain available while the current slot is assembled. -/
def OtherStorage (s : MachineState) (x : graph.Assignment) (dest : Name) : Prop :=
  ∀ n : Name, n ≠ dest → MemBits s (BitVec.ofNat 64 (slotAddress n)) (x n.fin)

theorem OtherStorage.frame {s t : MachineState} {x : graph.Assignment} {dest : Name}
    (stored : OtherStorage s x dest) (frame : SlotFrame s t dest) : OtherStorage t x dest := by
  intro n different
  apply frame.other different.symm (x n.fin)
  · rw [graph_len_fin]
    exact (node_length_bound n).trans (by decide)
  · exact stored n different

theorem OtherStorage.low {s : MachineState} {x : graph.Assignment} {dest : Name}
    (stored : OtherStorage s x dest) (n : Name) (different : n ≠ dest) :
    MemBits s (BitVec.ofNat 64 (slotAddress n)) (trunc (x n.fin)) := by
  have bound : 0 + 128 ≤ graph.len n.fin := by
    rw [graph_len_fin]
    exact node_length_positive n
  have h := memBits_extract (start := 0) (len := 128) (stored n different) (by decide) bound
  have he : (x n.fin).extractLsb' 0 128 = trunc (x n.fin) := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp [trunc, hi]
  rw [show BitVec.ofNat 64 (slotAddress n) + BitVec.ofNat 64 (0 / 8) =
    BitVec.ofNat 64 (slotAddress n) from BitVec.add_zero _, he] at h
  exact h

/-- An in-progress concatenation, together with all child values it may still read. -/
def Packing {width : ℕ} (s : MachineState) (dest : Name) (x : graph.Assignment)
    (value : BitVec width) : Prop :=
  s.getReg .x18 = BitVec.ofNat 64 (slotAddress dest) ∧ OtherStorage s x dest ∧
    MemBits s (BitVec.ofNat 64 (slotAddress dest)) value

/-- Each child copy extends the current packed prefix by one 128-bit word. -/
theorem Packing.append {width : ℕ} {s : MachineState} {dest : Name} {x : graph.Assignment}
    {value : BitVec width} (packing : Packing s dest x value) (child : Name)
    (different : child ≠ dest) (bounded : width ≤ 896) (wordAligned : width % 128 = 0) :
    Packing ((copyChild child (width / 8)).foldl execInstrBr s) dest x
      (trunc (x child.fin) ++ value) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [copyChild_register _ _ _ .x18 (by decide) (by decide) (by decide)]
    exact packing.1
  · apply packing.2.1.frame
    have h : width / 8 = 8 * (width / 64) := by omega
    rw [h]
    exact copyChild_slotFrame s dest child (width / 64) (by omega) packing.1
  · exact copyChild_append s dest child value _ bounded (by omega) packing.1
      packing.2.2 (packing.2.1.low child different)

/-- The final tag preserves every child slot and completes the hash input. -/
theorem Packing.tag {width : ℕ} {s : MachineState} {dest : Name} {x : graph.Assignment}
    {value : BitVec width} (packing : Packing s dest x value) (tag : BitVec 16)
    (bounded : width ≤ 896) (wordAligned : width % 64 = 0)
    (literal : (literalValue tag.toNat).truncate 16 = tag) :
    Packing ((writeTag tag (width / 8)).foldl execInstrBr s) dest x (tag ++ value) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [writeTag_register _ _ _ .x18 (by decide)]
    exact packing.1
  · apply packing.2.1.frame
    have h : width / 8 = 8 * (width / 64) := by omega
    rw [h]
    exact writeTag_slotFrame s dest tag (width / 64) (by omega) literal packing.1
  · exact writeTag_append s dest value tag bounded wordAligned literal packing.1 packing.2.2

/-- A new packed prefix starts with no bits. -/
theorem packing_empty (s : MachineState) (dest : Name) (x : graph.Assignment)
    (destination : s.getReg .x18 = BitVec.ofNat 64 (slotAddress dest))
    (stored : OtherStorage s x dest) : Packing s dest x (0 : BitVec 0) := by
  exact ⟨destination, stored, fun i hi => by omega⟩

/-- The copy operation stores its child's low word. -/
theorem operation_copy_packing (s : MachineState) (dest child : Name) (x : graph.Assignment)
    (destination : s.getReg .x18 = BitVec.ofNat 64 (slotAddress dest))
    (stored : OtherStorage s x dest) (different : child ≠ dest) :
    Packing ((operation (.copy child)).foldl execInstrBr s) dest x (trunc (x child.fin)) := by
  simpa only [operation, Nat.zero_div, BitVec.append_zero_width] using
    (packing_empty s dest x destination stored).append child different (by decide) (by decide)

/-- A tagged chain input consists of the child word followed in memory by its tag. -/
theorem operation_tagged1_packing (s : MachineState) (dest child : Name) (x : graph.Assignment)
    (tag : BitVec 16) (literal : (literalValue tag.toNat).truncate 16 = tag)
    (destination : s.getReg .x18 = BitVec.ofNat 64 (slotAddress dest))
    (stored : OtherStorage s x dest) (different : child ≠ dest) :
    Packing ((operation (.tagged1 tag child)).foldl execInstrBr s) dest x
      (tag ++ trunc (x child.fin)) := by
  have copied := operation_copy_packing s dest child x destination stored different
  simpa only [operation, List.foldl_append] using copied.tag tag (by decide) (by decide) literal

/-- Three child words occupy consecutive addresses in least-significant-first order. -/
theorem operation_tagged3_packing (s : MachineState) (dest a b c : Name) (x : graph.Assignment)
    (tag : BitVec 16) (literal : (literalValue tag.toNat).truncate 16 = tag)
    (destination : s.getReg .x18 = BitVec.ofNat 64 (slotAddress dest))
    (stored : OtherStorage s x dest) (ha : a ≠ dest) (hb : b ≠ dest) (hc : c ≠ dest) :
    Packing ((operation (.tagged3 tag a b c)).foldl execInstrBr s) dest x
      (tag ++ cat3 (trunc (x a.fin)) (trunc (x b.fin)) (trunc (x c.fin))) := by
  have first := operation_copy_packing s dest c x destination stored hc
  have second := first.append b hb (by decide) (by decide)
  have third := second.append a ha (by decide) (by decide)
  have final := third.tag tag (by decide) (by decide) literal
  have assoc (u v w : BitVec 128) : cat3 u v w = u ++ (v ++ w) := by
    simp only [cat3, BitVec.append_assoc, BitVec.cast_cast, BitVec.cast_eq]
  rw [assoc]
  simp only [operation, List.foldl_append]
  exact final

/-- Seven child words followed by a tag implement the root's 912-bit input. -/
theorem operation_tagged7_packing (s : MachineState) (dest : Name) (children : Fin 7 → Name)
    (x : graph.Assignment) (tag : BitVec 16)
    (literal : (literalValue tag.toNat).truncate 16 = tag)
    (destination : s.getReg .x18 = BitVec.ofNat 64 (slotAddress dest))
    (stored : OtherStorage s x dest) (different : ∀ l, children l ≠ dest) :
    Packing ((operation (.tagged7 tag children)).foldl execInstrBr s) dest x
      (tag ++ cat7 (fun l => trunc (x (children l).fin))) := by
  have first := operation_copy_packing s dest (children 6) x destination stored (different 6)
  have second := first.append (children 5) (different 5) (by decide) (by decide)
  have third := second.append (children 4) (different 4) (by decide) (by decide)
  have fourth := third.append (children 3) (different 3) (by decide) (by decide)
  have fifth := fourth.append (children 2) (different 2) (by decide) (by decide)
  have sixth := fifth.append (children 1) (different 1) (by decide) (by decide)
  have seventh := sixth.append (children 0) (different 0) (by decide) (by decide)
  have final := seventh.tag tag (by decide) (by decide) literal
  have expanded : (List.finRange 7).reverse = [6, 5, 4, 3, 2, 1, 0] := by decide
  have assoc (v : Fin 7 → BitVec 128) :
      cat7 v = v 0 ++ (v 1 ++ (v 2 ++ (v 3 ++ (v 4 ++ (v 5 ++ v 6))))) := by
    simp only [cat7, BitVec.append_assoc, BitVec.cast_cast, BitVec.cast_eq]
  rw [assoc]
  simp only [operation, expanded, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.foldl_append]
  exact final

/-- A graph-typed source value is the exact query issued by HASH. -/
theorem hashSetup_input_graph (s : MachineState) (source : Name) (x : graph.Assignment)
    (represented : MemBits s (BitVec.ofNat 64 (slotAddress source)) (x source.fin)) :
    Riscv.hashInput ((hashSetup source).foldl execInstrBr s) =
      ⟨graph.len source.fin, x source.fin⟩ := by
  have regs := hashSetup_registers s source
  apply hashInput_of_memBits regs.1
  · rw [regs.2.1, BitVec.toNat_ofNat, graph_len_fin]
    apply Nat.mod_eq_of_lt
    have := node_length_bound source
    omega
  · exact memBits_of_mem_eq (hashSetup_memory s source) represented

/-- The operation's hash input agrees with the graph-typed source value. -/
theorem operationEffect_hash_graph (s : MachineState) (source : Name) (x : graph.Assignment)
    (represented : MemBits s (BitVec.ofNat 64 (slotAddress source)) (x source.fin)) :
    operationEffect s (.hash source) = (do
      let answer ← hash paperParams (x source.fin)
      return Riscv.writeHash ((hashSetup source).foldl execInstrBr s) answer) := by
  dsimp only [operationEffect]
  exact congrArg (fun q : Query => do
    let answer ← hash paperParams q.2
    return Riscv.writeHash ((hashSetup source).foldl execInstrBr s) answer)
    (hashSetup_input_graph s source x represented)

/-- The operation's resulting machine state as a function of its certified node value. -/
def nodeResult (s : MachineState) (n : Name) (value : BitVec (graph.len n.fin)) : MachineState :=
  match n with
  | .ch k t => Riscv.writeHash ((hashSetup (.ci k t)).foldl execInstrBr s) (value.setWidth 256)
  | .gh j => Riscv.writeHash ((hashSetup (.gc j)).foldl execInstrBr s) (value.setWidth 256)
  | .eh l => Riscv.writeHash ((hashSetup (.ec l)).foldl execInstrBr s) (value.setWidth 256)
  | .rh => Riscv.writeHash ((hashSetup .rc).foldl execInstrBr s) (value.setWidth 256)
  | n => (operation (nodeOp n)).foldl execInstrBr s

private theorem setWidth_cast_self {a b : ℕ} (h : a = b) (value : BitVec a) :
    (value.cast h).setWidth a = value := by
  subst h
  exact BitVec.setWidth_eq value

/-- The compiled operation and the forest interpreter make identical oracle calls. -/
theorem operationEffect_eq (s : MachineState) (n : Name) (x : graph.Assignment)
    (stored : OtherStorage s x n) :
    operationEffect s (nodeOp n) = nodeResult s n <$> evalName x n := by
  cases n with
  | src k => rfl
  | ci k t => simp only [nodeOp, operationEffect, evalName, map_pure]; rfl
  | cv k t => simp only [nodeOp, operationEffect, evalName, map_pure]; rfl
  | gc j => simp only [nodeOp, operationEffect, evalName, map_pure]; rfl
  | gv j => simp only [nodeOp, operationEffect, evalName, map_pure]; rfl
  | ec l => simp only [nodeOp, operationEffect, evalName, map_pure]; rfl
  | ev l => simp only [nodeOp, operationEffect, evalName, map_pure]; rfl
  | rc => simp only [nodeOp, operationEffect, evalName, map_pure]; rfl
  | ch k t =>
    rw [show nodeOp (.ch k t) = .hash (.ci k t) from rfl,
      operationEffect_hash_graph s (.ci k t) x (stored _ (by simp))]
    simp only [evalName, map_eq_bind_pure_comp, bind_assoc, Function.comp_apply, pure_bind]
    apply congrArg (fun f => hash paperParams (x (ci k t).fin) >>= f)
    funext y
    apply congrArg pure
    simp only [Function.comp_apply, nodeResult]
    congr 1 <;> exact (setWidth_cast_self _ y).symm
  | gh j =>
    rw [show nodeOp (.gh j) = .hash (.gc j) from rfl,
      operationEffect_hash_graph s (.gc j) x (stored _ (by simp))]
    simp only [evalName, map_eq_bind_pure_comp, bind_assoc, Function.comp_apply, pure_bind]
    apply congrArg (fun f => hash paperParams (x (gc j).fin) >>= f)
    funext y
    apply congrArg pure
    simp only [Function.comp_apply, nodeResult]
    congr 1 <;> exact (setWidth_cast_self _ y).symm
  | eh l =>
    rw [show nodeOp (.eh l) = .hash (.ec l) from rfl,
      operationEffect_hash_graph s (.ec l) x (stored _ (by simp))]
    simp only [evalName, map_eq_bind_pure_comp, bind_assoc, Function.comp_apply, pure_bind]
    apply congrArg (fun f => hash paperParams (x (ec l).fin) >>= f)
    funext y
    apply congrArg pure
    simp only [Function.comp_apply, nodeResult]
    congr 1 <;> exact (setWidth_cast_self _ y).symm
  | rh =>
    rw [show nodeOp .rh = .hash .rc from rfl,
      operationEffect_hash_graph s .rc x (stored _ (by simp))]
    simp only [evalName, map_eq_bind_pure_comp, bind_assoc, Function.comp_apply, pure_bind]
    apply congrArg (fun f => hash paperParams (x rc.fin) >>= f)
    funext y
    apply congrArg pure
    simp only [Function.comp_apply, nodeResult]
    congr 1 <;> exact (setWidth_cast_self _ y).symm

end OptimalOTS.RiscvUpperProgram.Direct
