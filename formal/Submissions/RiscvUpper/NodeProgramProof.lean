import Submissions.RiscvUpper.NodeProgram
import Submissions.RiscvUpper.ForestVerifierProof
import Submissions.RiscvUpper.MachineMemory
import Submissions.RiscvUpper.AssemblyMacros
import Submissions.RiscvUpper.CopyProof
import Submissions.RiscvUpper.StructuredPure
import Submissions.RiscvUpper.HashOutput

/-! Instruction and memory refinements for the direct forest program. -/

namespace OptimalOTS.RiscvUpperProgram.Direct

open RiscvZkvm.Rv64 Forest Forest.Name RiscvUpperForest.ForestVerifier OracleComp

/-- Setup immediately preceding a node's hash instruction. -/
def hashSetup (source : Name) : Code :=
  constant .x10 (slotAddress source) ++ constant .x11 source.len ++
    [.ADDI .x12 .x18 0, .ADDI .x5 .x0 1]

theorem operation_hash (source : Name) : operation (.hash source) = hashSetup source ++ [.ECALL] := by
  simp [operation, hashSetup, List.append_assoc]

/-- Execute the ordinary instructions of an operation and its optional hash. -/
def operationEffect (s : MachineState) (op : NodeOp) :
    OracleComp (Spec paperParams) MachineState :=
  match op with
  | .hash source => do
      let prepared := (hashSetup source).foldl execInstrBr s
      let answer ← hash paperParams (Riscv.hashInput prepared).2
      return Riscv.writeHash prepared answer
  | _ => pure ((operation op).foldl execInstrBr s)

/-- All ordinary memory accesses and the optional hash boundary are valid. -/
def OperationReady (s : MachineState) (op : NodeOp) : Prop :=
  match op with
  | .hash source => Riscv.LinearReady s (hashSetup source) ∧
      Riscv.hashArgumentsValid ((hashSetup source).foldl execInstrBr s) = true
  | _ => Riscv.LinearReady s (operation op)

theorem hashSetup_call (s : MachineState) (source : Name) :
    ((hashSetup source).foldl execInstrBr s).getReg .x5 = Riscv.hashCall := by
  simp only [hashSetup, List.foldl_append, List.foldl_cons, List.foldl_nil, execInstrBr,
    MachineState.getReg_setPC, MachineState.getReg_setReg_eq (by decide : Reg.x5 ≠ .x0)]
  rfl

/-- A node operation's instruction sequence realizes its exact oracle computation. -/
theorem operation_observe (s : MachineState) (op : NodeOp) (fuel : ℕ)
    (located : Riscv.CodeAt s s.pc (operation op)) (ready : OperationReady s op) :
    Riscv.observe ((operation op).length + fuel) s = (do
      let next ← operationEffect s op
      Riscv.observe fuel next) := by
  cases op with
  | hash source =>
    rw [operation_hash] at located ⊢
    obtain ⟨prepared, valid⟩ := ready
    have rest : Riscv.CodeAt ((hashSetup source).foldl execInstrBr s)
        ((hashSetup source).foldl execInstrBr s).pc [.ECALL] := by
      rw [Riscv.linear_fold_pc _ _ prepared]
      exact located.append_right.code_eq (Riscv.fold_code _ _)
    simp only [List.length_append, List.length_singleton]
    rw [Nat.add_assoc, Riscv.observe_linear (1 + fuel) s _ located.append_left prepared]
    rw [Nat.add_comm 1 fuel, Riscv.observe_hash _ _ rest.head (hashSetup_call _ _) valid]
    simp only [operationEffect, bind_assoc, pure_bind]
  | zero => simpa only [operationEffect, pure_bind] using Riscv.observe_linear fuel s _ located ready
  | copy source => simpa only [operationEffect, pure_bind] using Riscv.observe_linear fuel s _ located ready
  | tagged1 tag source => simpa only [operationEffect, pure_bind] using Riscv.observe_linear fuel s _ located ready
  | tagged3 tag a b c => simpa only [operationEffect, pure_bind] using Riscv.observe_linear fuel s _ located ready
  | tagged7 tag children => simpa only [operationEffect, pure_bind] using Riscv.observe_linear fuel s _ located ready

/-- Copying a word reads both source doublewords before writing the destination. -/
theorem copy128_memory (s : MachineState) (src : Reg) (srcOff dstOff : ℕ)
    (src26 : src ≠ .x26)
    (hsrc : srcOff + 8 < 2048) (hdst : dstOff + 8 < 2048) :
    ((copy128 src srcOff .x18 dstOff).foldl execInstrBr s).mem =
      ((s.setMem (s.getReg .x18 + BitVec.ofNat 64 dstOff)
        (s.getMem (s.getReg src + BitVec.ofNat 64 srcOff))).setMem
          (s.getReg .x18 + BitVec.ofNat 64 (dstOff + 8))
          (s.getMem (s.getReg src + BitVec.ofNat 64 (srcOff + 8)))).mem := by
  have h1 := signExtend12_nonnegative srcOff (by omega)
  have h2 := signExtend12_nonnegative (srcOff + 8) hsrc
  have h3 := signExtend12_nonnegative dstOff (by omega)
  have h4 := signExtend12_nonnegative (dstOff + 8) hdst
  simp only [copy128, List.foldl_cons, List.foldl_nil, execInstrBr,
    h1, h2, h3, h4, MachineState.getReg_setPC,
    MachineState.getReg_setReg_ne _ .x26 src _ src26.symm,
    MachineState.getReg_setReg_ne _ .x27 .x18 _ (by decide),
    MachineState.getReg_setReg_ne _ .x26 .x18 _ (by decide),
    MachineState.getReg_setReg_ne _ .x27 .x26 _ (by decide),
    MachineState.getReg_setReg_eq (by decide : Reg.x26 ≠ .x0),
    MachineState.getMem_setPC, MachineState.getMem_setReg]
  rfl

/-- The decoded positions are stored as natural 64-bit words. -/
def PositionMemory (s : MachineState) (positions : Fin 63 → Fin 15) : Prop :=
  ∀ k : Fin 63, k.val < 36 →
    s.getMem (s.getReg .x8 + BitVec.ofNat 64 (8 * k.val)) = BitVec.ofNat 64 (positions k).val

private theorem literal12 (n : ℕ) (h : n < 2048) :
    constant .x27 n = [.ADDI .x27 .x0 (BitVec.ofNat 12 n)] := by
  simp [constant, h]

/-- The guard instructions compute the exact disclosure and evaluation predicates. -/
theorem guards_values (s : MachineState) (positions : Fin 63 → Fin 15) (n : Name)
    (memory : PositionMemory s positions) :
    ((guards n).foldl execInstrBr s).getReg .x24 =
        BitVec.ofNat 64 (disclosed positions n).toNat ∧
    ((guards n).foldl execInstrBr s).getReg .x25 =
        BitVec.ofNat 64 (evaluated positions n).toNat := by
  have sext (n : ℕ) (hn : n < 2048) :
      (BitVec.ofNat 12 n).signExtend 64 = BitVec.ofNat 64 n :=
    signExtend12_nonnegative n hn
  have ht (t : Fin 14) : t.val < 2048 := by omega
  have hts (t : Fin 14) : t.val + 1 < 2048 := by omega
  have hoff (k : Fin 63) : 8 * k.val < 2048 := by omega
  have word (n : ℕ) (hn : n < 2048) : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  cases n with
  | src k =>
    by_cases hk : k.val < 36
    · have hm := memory k hk
      change s.getMem (s.regs .x8 + BitVec.ofNat 64 (8 * k.val)) = _ at hm
      have hp : (positions k).val < 2048 := by have := (positions k).isLt; omega
      simp [guards, hk, disclosed, evaluated, execInstrBr, MachineState.getReg,
        MachineState.setReg, MachineState.setPC, signExtend12, sext _ (hoff k), hm,
        BitVec.ult, word _ hp, -Fin.val_eq_zero_iff]
      by_cases hz : (positions k).val = 0 <;> simp [hz]
    · simp [guards, hk, disclosed, evaluated, execInstrBr, MachineState.getReg,
        MachineState.setReg, MachineState.setPC, signExtend12]
  | ci k t | ch k t =>
    by_cases hk : k.val < 36
    · have hm := memory k hk
      change s.getMem (s.regs .x8 + BitVec.ofNat 64 (8 * k.val)) = _ at hm
      have hp : (positions k).val < 2048 := by have := (positions k).isLt; omega
      simp [guards, hk, constant, ht, disclosed, evaluated,
        execInstrBr, MachineState.getReg, MachineState.setReg, MachineState.setPC,
        BitVec.ult, signExtend12, sext _ (hoff k), sext _ (ht t), hm,
        word _ hp, word _ (ht t)]
      by_cases h : t.val < (positions k).val
      · simp [h, Nat.not_le.mpr h]
      · simp [h, Nat.le_of_not_gt h]
    · simp [guards, hk, disclosed, evaluated, execInstrBr, MachineState.getReg,
        MachineState.setReg, MachineState.setPC, signExtend12]
  | cv k t =>
    by_cases hk : k.val < 36
    · have hm := memory k hk
      change s.getMem (s.regs .x8 + BitVec.ofNat 64 (8 * k.val)) = _ at hm
      have hp : (positions k).val < 2048 := by have := (positions k).isLt; omega
      simp [guards, hk, constant, ht, hts, disclosed, evaluated,
        execInstrBr, MachineState.getReg, MachineState.setReg, MachineState.setPC,
        BitVec.ult, signExtend12, sext _ (hoff k), sext _ (ht t), sext _ (hts t), hm,
        word _ hp, word _ (ht t), word _ (hts t)]
      constructor
      · by_cases h : (positions k).val = t.val + 1 <;> simp [h]
      · by_cases h : t.val < (positions k).val
        · simp [h, Nat.not_le.mpr h]
        · simp [h, Nat.le_of_not_gt h]
    · simp [guards, hk, disclosed, evaluated, execInstrBr, MachineState.getReg,
        MachineState.setReg, MachineState.setPC, signExtend12]
  | gc j | gh j | gv j => fin_cases j <;> exact ⟨rfl, rfl⟩
  | ec l | eh l | ev l => fin_cases l <;> exact ⟨rfl, rfl⟩
  | rc | rh => exact ⟨rfl, rfl⟩

set_option maxRecDepth 100000 in
/-- Literal materialization is exact at every node slot address. -/
theorem slotAddress_literal (n : Name) :
    literalValue (slotAddress n) = BitVec.ofNat 64 (slotAddress n) := by
  have checked : ∀ v : Fin N,
      literalValue (slotAddress (ofFin v)) = BitVec.ofNat 64 (slotAddress (ofFin v)) := by
    decide +kernel
  simpa only [ofFin_fin] using checked n.fin

/-- The slot-clearing block writes sixteen zero doublewords. -/
theorem clearSlot_memory (s : MachineState) :
    (clearSlot.foldl execInstrBr s).mem =
      (s.writeWords (s.getReg .x18) (List.replicate 16 0)).mem := by
  simp [clearSlot, List.range_succ, execInstrBr, MachineState.getReg,
    MachineState.setPC, MachineState.setMem, MachineState.writeWords,
    List.replicate_succ, signExtend12, BitVec.add_assoc]

/-- Clearing a slot preserves every register. -/
theorem clearSlot_registers (s : MachineState) (r : Reg) :
    (clearSlot.foldl execInstrBr s).getReg r = s.getReg r := by
  simp [clearSlot, List.range_succ, execInstrBr, MachineState.getReg,
    MachineState.setPC, MachineState.setMem]

/-- Guard evaluation leaves memory and the program counter's instruction image unchanged. -/
theorem guards_memory (s : MachineState) (n : Name) :
    ((guards n).foldl execInstrBr s).mem = s.mem := by
  cases n <;> simp [guards, constant, List.foldl_append, execInstrBr,
    MachineState.setReg, MachineState.setPC] <;> split_ifs <;> rfl

/-- An operation can be followed by any continuation with a sufficient remaining budget. -/
theorem operation_cps (s : MachineState) (op : NodeOp) (budget tail : ℕ)
    (continuation : MachineState → OracleComp (Spec paperParams) (Option Bool))
    (located : Riscv.CodeAt s s.pc (operation op)) (ready : OperationReady s op)
    (enough : (operation op).length + tail ≤ budget)
    (rest : ∀ next ∈ support (operationEffect s op), ∀ fuel, tail ≤ fuel →
      Riscv.observe fuel next = continuation next) :
    Riscv.observe budget s = operationEffect s op >>= continuation := by
  have hb : budget = (operation op).length + (budget - (operation op).length) := by omega
  rw [hb, operation_observe s op _ located ready]
  apply bind_congr_of_forall_mem_support
  intro next hn
  exact rest next hn _ (by omega)

/-- Node values occupy at most fifteen of their sixteen allocated doublewords. -/
theorem node_length_bound (n : Name) : n.len ≤ 912 := by cases n <;> simp [Name.len]

/-- All slot-relative doubleword accesses lie in admitted memory. -/
theorem slot_access (n : Name) (j : ℕ) (hj : j < 16) :
    isValidDwordAccess (BitVec.ofNat 64 (slotAddress n) + BitVec.ofNat 64 (8 * j)) = true := by
  have bounds := slotAddress_bounds n
  have aligned := slotAddress_aligned n
  simp only [isValidDwordAccess, isAligned8, isValidMemAddr, MEM_START, MEM_END,
    INPUT_MEM_START, INPUT_MEM_END, RAM_MEM_START, RAM_MEM_END,
    BitVec.toNat_add, BitVec.toNat_ofNat, Bool.and_eq_true, Bool.or_eq_true,
    decide_eq_true_eq, beq_iff_eq]
  omega

/-- A halfword store writes exactly its low sixteen bits at an aligned address. -/
theorem memBits_setHalfword (s : MachineState) (base : Word) (value : BitVec 16)
    (aligned : alignToDword base = base) :
    MemBits (s.setHalfword base value) base value := by
  have offset : byteOffset base = 0 := by
    rw [byteOffset_eq_mod]
    exact (aligned_iff base).mp aligned
  have stored : (s.setHalfword base value).getMem base =
      replaceHalfword (s.getMem base) 0 value := by
    simp only [MachineState.setHalfword, aligned, offset, Nat.zero_div,
      MachineState.getMem_setMem_eq]
  have low (word : Word) (v : BitVec 16) :
      (replaceHalfword word 0 v).extractLsb' 0 16 = v := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    interval_cases i <;> simp [replaceHalfword]
  have h := memBits_extract (start := 0) (len := 16)
    (memBits_word (s.setHalfword base value) base aligned) (by decide) (by decide)
  have address : base + BitVec.ofNat 64 (0 / 8) = base := BitVec.add_zero base
  rw [address, stored, low] at h
  exact h

/-- Distinct node slots have disjoint doubleword addresses. -/
theorem slot_word_ne (n m : Name) (j k : ℕ) (hjm : j < 16) (hkm : k < 16)
    (different : n ≠ m) :
    BitVec.ofNat 64 (slotAddress n) + BitVec.ofNat 64 (8 * j) ≠
      BitVec.ofNat 64 (slotAddress m) + BitVec.ofNat 64 (8 * k) := by
  intro equal
  have hn := slotAddress_bounds n
  have hm := slotAddress_bounds m
  have h := congrArg BitVec.toNat equal
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at h
  have hi : n.idx = m.idx := by
    unfold slotAddress slotsBase at hn hm h
    omega
  exact different (Name.idx_injective hi)

/-- The word containing a slot's bit is still inside that slot. -/
theorem slot_bit_word (n : Name) (i : ℕ) (hi : i < 1024) :
    alignToDword (BitVec.ofNat 64 (slotAddress n) + BitVec.ofNat 64 (i / 8)) =
      BitVec.ofNat 64 (slotAddress n) + BitVec.ofNat 64 (8 * (i / 64)) := by
  have hb := slotAddress_bounds n
  have ha := slotAddress_aligned n
  apply BitVec.eq_of_toNat_eq
  simp only [alignToDword_toNat, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- Stores into one node slot preserve every represented value in a different slot. -/
theorem memBits_setSlotWord {width : ℕ} (s : MachineState) (n m : Name) (j : ℕ)
    (word : Word) (value : BitVec width) (small : width ≤ 1024) (hj : j < 16)
    (different : n ≠ m) (represented : MemBits s (BitVec.ofNat 64 (slotAddress m)) value) :
    MemBits (s.setMem (BitVec.ofNat 64 (slotAddress n) + BitVec.ofNat 64 (8 * j)) word)
      (BitVec.ofNat 64 (slotAddress m)) value := by
  apply memBits_setMem word represented
  intro i hi
  rw [slot_bit_word m i (by omega)]
  exact slot_word_ne m n (i / 64) j (by omega) hj different.symm

/-- Copying a child transports its low 128 bits into the destination slot. -/
theorem copyChild_memBits (s : MachineState) (child : Name) (off : ℕ)
    (value : BitVec 128) (source : MemBits s (BitVec.ofNat 64 (slotAddress child)) value)
    (destAligned : alignToDword (s.getReg .x18 + BitVec.ofNat 64 off) =
      s.getReg .x18 + BitVec.ofNat 64 off) (small : off + 8 < 2048) :
    MemBits ((copyChild child off).foldl execInstrBr s)
      (s.getReg .x18 + BitVec.ofNat 64 off) value := by
  let prepared := (constant .x7 (slotAddress child)).foldl execInstrBr s
  have srcReg : prepared.getReg .x7 = BitVec.ofNat 64 (slotAddress child) := by
    rw [constant_value s .x7 _ (by decide), slotAddress_literal]
  have dstReg : prepared.getReg .x18 = s.getReg .x18 :=
    constant_preserves s .x7 .x18 _ (by decide)
  have srcAligned : alignToDword (BitVec.ofNat 64 (slotAddress child)) =
      BitVec.ofNat 64 (slotAddress child) := by
    apply (aligned_iff _).mpr
    have h := slotAddress_aligned child
    have hb := slotAddress_bounds child
    simp only [BitVec.toNat_ofNat]
    omega
  have srcPoint : prepared.getReg .x7 + BitVec.ofNat 64 0 =
      BitVec.ofNat 64 (slotAddress child) := by
    rw [srcReg]
    exact BitVec.add_zero _
  have sourcePrepared : MemBits prepared
      (prepared.getReg .x7 + BitVec.ofNat 64 0) value := by
    rw [srcPoint]
    exact memBits_of_mem_eq (constant_mem s .x7 (slotAddress child)) source
  have moved := copy128_memBits prepared .x7 .x18 0 off (by decide) (by decide) (by decide)
    (by decide) small (by rw [srcPoint]; exact srcAligned)
    (by rw [dstReg]; exact destAligned) value sourcePrepared
  rw [dstReg] at moved
  simpa only [copyChild, List.foldl_append] using moved

/-- Pure setup and the optional disclosure read, before a node's computation branch. -/
def nodePrelude (n : Name) : PureBlock :=
  .seq (.linear (constant .x18 (slotAddress n) ++ clearSlot ++ guards n))
    (.guard false .x24 (.linear readDisclosure))

theorem nodeCode_parts (n : Name) :
    nodeCode n = (nodePrelude n).code ++ whenNonzero .x25 (operation (nodeOp n)) := rfl

/-- The actual machine-state effect of the optional computation branch. -/
def guardEffect (s : MachineState) (op : NodeOp) :
    OracleComp (Spec paperParams) MachineState :=
  if s.getReg .x25 = 0 then
    pure (s.setPC (s.pc + BitVec.ofNat 64 (4 * ((operation op).length + 1))))
  else operationEffect (s.setPC (s.pc + 4)) op

/-- The real node code, interpreted compositionally while retaining each hash query. -/
def nodeEffect (s : MachineState) (n : Name) : OracleComp (Spec paperParams) MachineState :=
  guardEffect ((nodePrelude n).eval s) (nodeOp n)

/-- Readiness of the two node regions at their actual intermediate states. -/
def NodeReady (s : MachineState) (n : Name) : Prop :=
  (nodePrelude n).Ready s ∧
  (let prepared := (nodePrelude n).eval s
   prepared.getReg .x25 ≠ 0 → OperationReady (prepared.setPC (prepared.pc + 4)) (nodeOp n))

private theorem constant_length (r : Reg) (n : ℕ) : (constant r n).length ≤ 2 := by
  unfold constant
  split <;> simp

private theorem copyChild_length (n : Name) (off : ℕ) : (copyChild n off).length ≤ 6 := by
  simp only [copyChild, List.length_append]
  have h := constant_length .x7 (slotAddress n)
  change (constant .x7 (slotAddress n)).length + 4 ≤ 6
  omega

private theorem writeTag_length (tag : BitVec 16) (off : ℕ) : (writeTag tag off).length ≤ 3 := by
  simp only [writeTag, List.length_append, List.length_singleton]
  have h := constant_length .x26 tag.toNat
  omega

/-- Every operation uses at most 45 instructions. -/
theorem operation_length_bound (op : NodeOp) : (operation op).length ≤ 45 := by
  cases op with
  | zero => simp [operation]
  | copy source => exact (copyChild_length source 0).trans (by decide)
  | tagged1 tag source =>
    simp only [operation, List.length_append]
    have := copyChild_length source 0
    have := writeTag_length tag 16
    omega
  | tagged3 tag a b c =>
    simp only [operation, List.length_append]
    have := copyChild_length c 0
    have := copyChild_length b 16
    have := copyChild_length a 32
    have := writeTag_length tag 48
    omega
  | tagged7 tag children =>
    have bound : ((List.finRange 7).reverse.flatMap
        (fun l => copyChild (children l) (16 * (6 - l.val)))).length ≤ 42 := by
      rw [List.length_flatMap]
      have h := List.sum_le_card_nsmul ((List.finRange 7).reverse.map
        (fun l => (copyChild (children l) (16 * (6 - l.val))).length)) 6 (by
          intro v hv
          obtain ⟨l, _, rfl⟩ := List.mem_map.mp hv
          exact copyChild_length _ _)
      simpa using h
    have := writeTag_length tag 112
    simp only [operation, List.length_append]
    omega
  | hash source =>
    simp only [operation, List.length_append, List.length_cons, List.length_nil]
    have := constant_length .x10 (slotAddress source)
    have := constant_length .x11 source.len
    omega

/-- Every computation branch fits a short forward RISC-V branch. -/
theorem node_operation_short (n : Name) : (operation (nodeOp n)).length < 1023 := by
  have := operation_length_bound (nodeOp n)
  omega

/-- The optional operation composes with any sufficiently budgeted continuation. -/
theorem guard_cps (s : MachineState) (op : NodeOp) (budget tail : ℕ)
    (continuation : MachineState → OracleComp (Spec paperParams) (Option Bool))
    (short : (operation op).length < 1023)
    (located : Riscv.CodeAt s s.pc (whenNonzero .x25 (operation op)))
    (ready : s.getReg .x25 ≠ 0 → OperationReady (s.setPC (s.pc + 4)) op)
    (enough : (operation op).length + 1 + tail ≤ budget)
    (rest : ∀ next ∈ support (guardEffect s op), ∀ fuel, tail ≤ fuel →
      Riscv.observe fuel next = continuation next) :
    Riscv.observe budget s = guardEffect s op >>= continuation := by
  have hb : budget = (budget - 1) + 1 := by omega
  rw [hb, whenNonzero_observe (budget - 1) s .x25 (operation op) short located]
  by_cases zero : s.getReg .x25 = 0
  · rw [if_pos zero]
    simp only [guardEffect, if_pos zero, pure_bind]
    apply rest
    · simp only [guardEffect, if_pos zero, mem_support_pure_iff]
    · omega
  · rw [if_neg zero]
    simp only [guardEffect, if_neg zero]
    apply operation_cps _ op (budget - 1) tail continuation
    · exact located.tail.code_eq (by rfl)
    · exact ready zero
    · omega
    · simpa only [guardEffect, if_neg zero] using rest

/-- The node compiler composes exact oracle computations; its budget includes all encoded paths. -/
theorem node_cps (s : MachineState) (n : Name) (budget tail : ℕ)
    (continuation : MachineState → OracleComp (Spec paperParams) (Option Bool))
    (located : Riscv.CodeAt s s.pc (nodeCode n)) (ready : NodeReady s n)
    (enough : (nodeCode n).length + tail ≤ budget)
    (rest : ∀ next ∈ support (nodeEffect s n), ∀ fuel, tail ≤ fuel →
      Riscv.observe fuel next = continuation next) :
    Riscv.observe budget s = nodeEffect s n >>= continuation := by
  rw [nodeCode_parts] at located enough
  obtain ⟨count, bound, executed⟩ :=
    PureBlock.steps (nodePrelude n) s ready.1 located.append_left
  have hb : budget = count + (budget - count) := by
    simp only [List.length_append, whenNonzero, List.length_cons] at enough
    omega
  rw [hb, executed.observe]
  apply guard_cps _ (nodeOp n) (budget - count) tail continuation (node_operation_short n)
  · rw [PureBlock.eval_pc _ _ ready.1]
    exact located.append_right.code_eq (PureBlock.eval_code _ _)
  · exact ready.2
  · simp only [List.length_append, whenNonzero, List.length_cons] at enough
    omega
  · exact rest

/-- Hash setup preserves the entire input memory. -/
theorem hashSetup_memory (s : MachineState) (source : Name) :
    ((hashSetup source).foldl execInstrBr s).mem = s.mem := by
  simp [hashSetup, List.foldl_append, execInstrBr, constant_mem,
    MachineState.setReg, MachineState.setPC]

/-- Direct HASH uses the source slot, its exact node length, and the current destination slot. -/
theorem hashSetup_registers (s : MachineState) (source : Name) :
    let prepared := (hashSetup source).foldl execInstrBr s
    prepared.getReg .x10 = BitVec.ofNat 64 (slotAddress source) ∧
    prepared.getReg .x11 = BitVec.ofNat 64 source.len ∧
    prepared.getReg .x12 = s.getReg .x18 := by
  have hl : source.len < 2048 := by have := node_length_bound source; omega
  simp only [hashSetup, List.foldl_append, List.foldl_cons, List.foldl_nil, execInstrBr,
    MachineState.getReg_setPC,
    MachineState.getReg_setReg_ne _ .x5 .x10 _ (by decide),
    MachineState.getReg_setReg_ne _ .x5 .x11 _ (by decide),
    MachineState.getReg_setReg_ne _ .x5 .x12 _ (by decide),
    MachineState.getReg_setReg_ne _ .x12 .x10 _ (by decide),
    MachineState.getReg_setReg_ne _ .x12 .x11 _ (by decide),
    MachineState.getReg_setReg_eq (by decide : Reg.x12 ≠ .x0),
    constant_preserves _ .x11 .x10 _ (by decide),
    constant_preserves _ .x11 .x18 _ (by decide),
    constant_preserves _ .x10 .x18 _ (by decide),
    constant_value _ .x10 _ (by decide), constant_value _ .x11 _ (by decide),
    slotAddress_literal, literalValue_small _ hl]
  simp only [true_and]
  exact BitVec.add_zero _

/-- The source slot supplies exactly the certified hash query, with no framing bytes. -/
theorem hashSetup_input (s : MachineState) (source : Name) (value : BitVec source.len)
    (represented : MemBits s (BitVec.ofNat 64 (slotAddress source)) value) :
    Riscv.hashInput ((hashSetup source).foldl execInstrBr s) = ⟨source.len, value⟩ := by
  have regs := hashSetup_registers s source
  apply hashInput_of_memBits regs.1
  · rw [regs.2.1, BitVec.toNat_ofNat]
    apply Nat.mod_eq_of_lt
    have := node_length_bound source
    omega
  · exact memBits_of_mem_eq (hashSetup_memory s source) represented

/-- Operation execution queries the same source value as the high-level node interpreter. -/
theorem operationEffect_hash (s : MachineState) (source : Name) (value : BitVec source.len)
    (represented : MemBits s (BitVec.ofNat 64 (slotAddress source)) value) :
    operationEffect s (.hash source) = (do
      let answer ← hash paperParams value
      return Riscv.writeHash ((hashSetup source).foldl execInstrBr s) answer) := by
  dsimp only [operationEffect]
  exact congrArg (fun q : Query => do
    let answer ← hash paperParams q.2
    return Riscv.writeHash ((hashSetup source).foldl execInstrBr s) answer)
    (hashSetup_input s source value represented)

/-- Every graph value is represented in its own fixed memory slot. -/
def NodeStorage (s : MachineState) (x : graph.Assignment) : Prop :=
  ∀ n : Name, MemBits s (BitVec.ofNat 64 (slotAddress n)) (x n.fin)

/-- Node slots contain at least a 128-bit word. -/
theorem node_length_positive (n : Name) : 128 ≤ n.len := by cases n <;> simp [Name.len]

/-- Every slot begins at an aligned doubleword. -/
theorem slot_aligned (n : Name) :
    alignToDword (BitVec.ofNat 64 (slotAddress n)) = BitVec.ofNat 64 (slotAddress n) := by
  apply (aligned_iff _).mpr
  have ha := slotAddress_aligned n
  have hb := slotAddress_bounds n
  simp only [BitVec.toNat_ofNat]
  omega

/-- Slot representation provides the truncated child words used by concatenation nodes. -/
theorem NodeStorage.low {s : MachineState} {x : graph.Assignment} (stored : NodeStorage s x)
    (n : Name) : MemBits s (BitVec.ofNat 64 (slotAddress n)) (trunc (x n.fin)) := by
  have bound : 0 + 128 ≤ graph.len n.fin := by
    rw [graph_len_fin]
    exact node_length_positive n
  have h := memBits_extract (start := 0) (len := 128) (stored n) (by decide) bound
  have he : (x n.fin).extractLsb' 0 128 = trunc (x n.fin) := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp [trunc, hi]
  rw [show BitVec.ofNat 64 (slotAddress n) + BitVec.ofNat 64 (0 / 8) =
    BitVec.ofNat 64 (slotAddress n) from BitVec.add_zero _, he] at h
  exact h

/-- A wordwise memory frame also preserves the represented bit vector. -/
theorem memBits_of_word_frame {width : ℕ} (s t : MachineState) (base : Word)
    (value : BitVec width) (represented : MemBits s base value)
    (frame : ∀ i, i < width → t.getMem (alignToDword (base + BitVec.ofNat 64 (i / 8))) =
      s.getMem (alignToDword (base + BitVec.ofNat 64 (i / 8)))) : MemBits t base value := by
  intro i hi
  simp only [MachineState.getByte, frame i hi]
  exact represented i hi

/-- Clearing one slot preserves every value in another slot. -/
theorem clearSlot_other {width : ℕ} (s : MachineState) (n m : Name)
    (value : BitVec width) (small : width ≤ 1024) (different : n ≠ m)
    (dest : s.getReg .x18 = BitVec.ofNat 64 (slotAddress n))
    (represented : MemBits s (BitVec.ofNat 64 (slotAddress m)) value) :
    MemBits (clearSlot.foldl execInstrBr s) (BitVec.ofNat 64 (slotAddress m)) value := by
  apply memBits_of_word_frame s _ _ value represented
  intro i hi
  have h := congrFun (clearSlot_memory s)
    (alignToDword (BitVec.ofNat 64 (slotAddress m) + BitVec.ofNat 64 (i / 8)))
  change (clearSlot.foldl execInstrBr s).getMem _ = _ at h
  rw [h]
  apply getMem_writeWords_of_disjoint
  intro j hj
  rw [dest, slot_bit_word m i (by omega)]
  exact slot_word_ne m n (i / 64) j (by omega) (by simpa using hj) different.symm

/-- The cleared destination represents the graph's zero value. -/
theorem clearSlot_zero (s : MachineState) (n : Name)
    (dest : s.getReg .x18 = BitVec.ofNat 64 (slotAddress n)) :
    MemBits (clearSlot.foldl execInstrBr s) (BitVec.ofNat 64 (slotAddress n)) (0 : BitVec n.len) := by
  apply memBits_of_words _ _ _ (slot_aligned n)
  intro j hj
  have hn := node_length_bound n
  have hj16 : j < 16 := by omega
  have h := congrFun (clearSlot_memory s)
    (BitVec.ofNat 64 (slotAddress n) + BitVec.ofNat 64 (8 * j))
  change (clearSlot.foldl execInstrBr s).getMem _ = _ at h
  rw [h]
  change (s.writeWords (s.getReg .x18) (List.replicate 16 0)).getMem _ = _
  rw [dest, getMem_writeWords_index _ _ _ (by norm_num) j (by simpa using hj16)]
  simp only [List.getElem_replicate]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp

end OptimalOTS.RiscvUpperProgram.Direct
