import Submissions.RiscvUpper.NodeProgram

/-!
# Compact RV64IM forest verifier

The image keeps one 32-byte slot per active chain: its current 128-bit value, the tag of the next
chain hash, and room for a complete hash answer, which HASH writes in place. Each chain is one
block: read the disclosed word, then jump into a table of fourteen hash steps at the step of the
disclosed position, exactly as the specification's sequential reader visits the chain's nodes.
Tree inputs are assembled in one scratch buffer.
-/

namespace OptimalOTS.RiscvUpperProgram.Compact

open RiscvZkvm.Rv64

def chainSlot (k : ℕ) : ℕ := 32 * k
def groupSlot (j : ℕ) : ℕ := 32 * j
def subtreeSlot (l : ℕ) : ℕ := 32 * l

/-- Hash step `t` of chain `k`: write the tag of `ch k t` after the slot's value and hash the
144-bit input in place. -/
def chainStep (k t : ℕ) : Code :=
  Direct.writeTag (BitVec.ofNat 16 (43 * k + 2 + 3 * t)) (chainSlot k + 16) ++ [.ECALL]

/-- The fourteen steps of chain `k`; the prologue jumps to the step of the disclosed position. -/
def chainTable (k : ℕ) : Code := (List.range 14).flatMap (chainStep k)

/-- Copy chain `k`'s disclosed word into its slot, point HASH at the slot, and jump over the
first `position` steps: `x28` is this block's address, the table starts 52 bytes later and each
step is 12 bytes. -/
def chainPrologue (k : ℕ) : Code :=
  [.AUIPC .x28 0] ++ copy128 .x9 (16 * k) .x18 (chainSlot k) ++
  [.ADDI .x10 .x18 (BitVec.ofNat 12 (chainSlot k)), .ADDI .x12 .x18 (BitVec.ofNat 12 (chainSlot k)),
   .LD .x26 .x8 (BitVec.ofNat 12 (8 * k)),
   .SLLI .x27 .x26 3, .SLLI .x26 .x26 2, .ADD .x27 .x27 .x26,
   .ADD .x27 .x27 .x28, .JALR .x0 .x27 52]

def chainBlock (k : ℕ) : Code := chainPrologue k ++ chainTable k

def chainSetup : Code :=
  constant .x18 chainsBase ++ constant .x9 (Riscv.signatureBase.toNat + 32) ++
  [.ADDI .x5 .x0 1, .ADDI .x11 .x0 144]

/-- The cursor passes the 36 disclosed chain words. -/
def chainsEnd : Code := [.ADDI .x9 .x9 576]

def chains : Code := chainSetup ++ (List.range 36).flatMap chainBlock ++ chainsEnd

/-- Three 128-bit values and a tag, last child lowest, in the scratch buffer at `x18`. -/
def tripleInput (src : Reg) (a b c tag : ℕ) : Code :=
  copy128 src c .x18 0 ++ copy128 src b .x18 16 ++ copy128 src a .x18 32 ++
  Direct.writeTag (BitVec.ofNat 16 tag) 48

def groupBlock (j : ℕ) : Code :=
  tripleInput .x19 (chainSlot (3 * j)) (chainSlot (3 * j + 1)) (chainSlot (3 * j + 2)) (2730 + j) ++
  [.ADDI .x10 .x18 0, .ADDI .x12 .x20 (BitVec.ofNat 12 (groupSlot j)), .ECALL]

def readGroup (j : ℕ) : Code := copy128 .x9 0 .x20 (groupSlot j) ++ [.ADDI .x9 .x9 16]

def treeSetup : Code :=
  constant .x18 scratchBase ++ constant .x19 chainsBase ++ constant .x20 groupsBase ++
  constant .x21 subtreesBase ++ [.ADDI .x11 .x0 400]

def groupHashes : Code :=
  (List.finRange 21).flatMap fun j => if j.val < 12 then groupBlock j.val else []

def groupReads : Code :=
  (List.finRange 21).flatMap fun j => if 12 ≤ j.val ∧ j.val < 15 then readGroup j.val else []

def groups : Code := treeSetup ++ groupHashes ++ groupReads

def subtreeBlock (l : ℕ) : Code :=
  tripleInput .x20 (groupSlot (3 * l)) (groupSlot (3 * l + 1)) (groupSlot (3 * l + 2)) (2779 + l) ++
  [.ADDI .x10 .x18 0, .ADDI .x12 .x21 (BitVec.ofNat 12 (subtreeSlot l)), .ECALL]

def readSubtree (l : ℕ) : Code := copy128 .x9 0 .x21 (subtreeSlot l) ++ [.ADDI .x9 .x9 16]

def subtreeHashes : Code :=
  (List.finRange 7).flatMap fun l => if l.val < 5 then subtreeBlock l.val else []

def subtreeReads : Code :=
  (List.finRange 7).flatMap fun l => if 5 ≤ l.val then readSubtree l.val else []

def subtrees : Code := subtreeHashes ++ subtreeReads

/-- The 912-bit root input: subtree `l` at byte `16 * (6 - l)`, then the tag. -/
def root : Code :=
  (List.finRange 7).reverse.flatMap (fun l => copy128 .x21 (subtreeSlot l.val) .x18 (16 * (6 - l.val))) ++
  Direct.writeTag (BitVec.ofNat 16 2794) 112 ++
  [.ADDI .x10 .x18 0, .ADDI .x11 .x0 912, .ADDI .x12 .x18 128, .ECALL]

/-- Compare the root answer's low 128 bits with the public key and halt. -/
def decision : Code :=
  constant .x7 Riscv.publicKeyBase.toNat ++
  [.LD .x26 .x18 128, .LD .x27 .x7 0, .XOR .x26 .x26 .x27,
   .LD .x24 .x18 136, .LD .x25 .x7 8, .XOR .x24 .x24 .x25,
   .OR .x10 .x26 .x24, .SLTIU .x10 .x10 1, .ADDI .x5 .x0 0, .ECALL]

def verifier : Code :=
  indexAndChecks ++ chains ++ groups ++ subtrees ++ root ++ decision

def image : Riscv.Image := ⟨verifier, []⟩

end OptimalOTS.RiscvUpperProgram.Compact
