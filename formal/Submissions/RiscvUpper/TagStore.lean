import Submissions.RiscvUpper.ForestVerifierProof
import Submissions.RiscvUpper.MachineMemory
import Submissions.RiscvUpper.AssemblyMacros
import Submissions.RiscvUpper.CopyProof
import Submissions.RiscvUpper.HashOutput

/-!
# Tag stores

Every hash input of the forest carries the 16-bit tweak of its node, which the image stores with
`writeTag`: a literal materialization followed by one halfword store. The store writes exactly the
tag's bits (`writeTag_memBits`), changes no other doubleword (`writeTag_frame`) and no register
other than its temporary (`writeTag_register`), and the literal is exact for every node's tweak
(`nodeTag_literal`).
-/

namespace OptimalOTS.RiscvUpperProgram

open RiscvZkvm.Rv64 Forest Forest.Name RiscvUpperForest.ForestVerifier

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

/-- Node slots contain at least a 128-bit word. -/
theorem node_length_positive (n : Name) : 128 ≤ n.len := by cases n <;> simp [Name.len]

end OptimalOTS.RiscvUpperProgram
