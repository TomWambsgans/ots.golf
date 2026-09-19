import Submissions.RiscvUpper.NodeProgram

/-!
# Compact RV64IM forest verifier

The image keeps one 32-byte slot per active chain: its current 128-bit value, the tag of the next
chain hash, and room for a complete hash answer, which HASH writes in place. Every level hashes the
evaluated chains in chain order, then reads the level's disclosed values, exactly as the
specification's sequential reader visits the nodes. Tree inputs are assembled in one scratch buffer.
-/

namespace OptimalOTS.RiscvUpperProgram.Compact

open RiscvZkvm.Rv64

def chainSlot (k : ℕ) : ℕ := 32 * k
def groupSlot (j : ℕ) : ℕ := 32 * j
def subtreeSlot (l : ℕ) : ℕ := 32 * l

/-- Read the next disclosed word into chain `k` when its position equals `p`. -/
def readChain (p k : ℕ) : Code :=
  [.LD .x26 .x8 (BitVec.ofNat 12 (8 * k))] ++ constant .x27 p ++ [.XOR .x26 .x26 .x27] ++
  whenZero .x26 (copy128 .x9 0 .x18 (chainSlot k) ++ [.ADDI .x9 .x9 16])

/-- Hash chain `k` at level `t` when its position is at most `t`. -/
def hashChain (t k : ℕ) : Code :=
  [.LD .x26 .x8 (BitVec.ofNat 12 (8 * k)), .SLTIU .x26 .x26 (BitVec.ofNat 12 (t + 1))] ++
  whenNonzero .x26 (Direct.writeTag (BitVec.ofNat 16 (126 + 189 * t + k)) (chainSlot k + 16) ++
    [.ADDI .x10 .x18 (BitVec.ofNat 12 (chainSlot k)),
     .ADDI .x12 .x18 (BitVec.ofNat 12 (chainSlot k)), .ECALL])

/-- The active chains, in the specification's chain order; inactive chains have no code. -/
def hashSweep (t : ℕ) : Code :=
  (List.finRange 63).flatMap fun k => if k.val < 36 then hashChain t k.val else []

def readSweep (p : ℕ) : Code :=
  (List.finRange 63).flatMap fun k => if k.val < 36 then readChain p k.val else []

def level (t : ℕ) : Code := hashSweep t ++ readSweep (t + 1)

def chainSetup : Code :=
  constant .x18 chainsBase ++ constant .x9 (Riscv.signatureBase.toNat + 32) ++
  [.ADDI .x5 .x0 1, .ADDI .x11 .x0 144]

def chains : Code :=
  chainSetup ++ readSweep 0 ++ (List.finRange 14).flatMap fun t => level t.val

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
