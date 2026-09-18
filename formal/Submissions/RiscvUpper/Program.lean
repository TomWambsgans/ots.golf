import OptimalOTS.RiscvMachine
import Submissions.RiscvUpper.Unrank

/-!
# Straight-line RV64IM forest verifier

All finite loops are unrolled. Conditional branches jump forward over one local block.
The decoder uses a table of base-15 composition counts, stored as 128-bit little-endian
integers. The remaining code parses the 41 disclosures and evaluates the forest in its
topological query order.
-/

namespace OptimalOTS.RiscvUpperProgram

open RiscvZkvm.Rv64

abbrev Code := List Instr

/-- Materialize a constant using real RV64I instructions. -/
def constant (rd : Reg) (n : ℕ) : Code :=
  if n < 2048 then [.ADDI rd .x0 (BitVec.ofNat 12 n)] else
    [.LUI rd (BitVec.ofNat 20 ((n + 2048) / 4096)), .ADDI rd rd (BitVec.ofNat 12 n)]

def whenZero (r : Reg) (body : Code) : Code :=
  .BNE r .x0 (BitVec.ofNat 13 (4 * (body.length + 1))) :: body

def whenNonzero (r : Reg) (body : Code) : Code :=
  .BEQ r .x0 (BitVec.ofNat 13 (4 * (body.length + 1))) :: body

def positionsBase : ℕ := 0x600000
def chainsBase : ℕ := 0x601000
def groupsBase : ℕ := 0x602000
def subtreesBase : ℕ := 0x603000
def scratchBase : ℕ := 0x604000

def reject : Code := [.ADDI .x5 .x0 0, .ADDI .x10 .x0 0, .ECALL]

/-- Copy a 128-bit value between register-relative, doubleword-aligned locations. -/
def copy128 (src : Reg) (srcOff : ℕ) (dst : Reg) (dstOff : ℕ) : Code :=
  [.LD .x26 src (BitVec.ofNat 12 srcOff), .LD .x27 src (BitVec.ofNat 12 (srcOff + 8)),
   .SD dst .x26 (BitVec.ofNat 12 dstOff), .SD dst .x27 (BitVec.ofNat 12 (dstOff + 8))]

/-- Hash the scratch input into the 32-byte scratch output at offset 128. -/
def hashScratch (bits : ℕ) : Code :=
  [.ADDI .x10 .x19 0] ++ constant .x11 bits ++
  [.ADDI .x12 .x19 128, .ADDI .x5 .x0 1, .ECALL]

def indexAndChecks : Code :=
  constant .x11 0 ++ constant .x19 scratchBase ++
  constant .x7 (Riscv.signatureBase.toNat) ++
  copy128 .x7 0 .x19 0 ++ copy128 .x7 16 .x19 16 ++
  constant .x7 (Riscv.messageBase.toNat) ++
  copy128 .x7 0 .x19 32 ++ copy128 .x7 16 .x19 48 ++
  hashScratch 512 ++
  [.LD .x20 .x19 128, .LD .x21 .x19 136, .SRLI .x26 .x21 51] ++
  whenNonzero .x26 reject ++ constant .x26 5504 ++
  [.XOR .x26 .x26 .x13] ++ whenNonzero .x26 reject

/-- Test one candidate digit in one row of the unranking table.
`x20/x21` hold the residual rank, `x22` the remaining sum, `x23` the selected flag. -/
def tryDigit (remaining slot digit : ℕ) : Code :=
  let subtract :=
    [.SLTU .x27 .x20 .x24, .SUB .x20 .x20 .x24,
     .SUB .x21 .x21 .x25, .SUB .x21 .x21 .x27]
  let choose :=
    constant .x7 (14 - digit) ++
    [.SD .x8 .x7 (BitVec.ofNat 12 (8 * slot)),
     .ADDI .x22 .x22 (-(BitVec.ofNat 12 digit)), .ADDI .x23 .x0 1]
  let readAndCompare :=
    constant .x6 (Riscv.dataBase.toNat + remaining * 122 * 16) ++
    [.ADDI .x7 .x22 (-(BitVec.ofNat 12 digit)), .SLLI .x7 .x7 4, .ADD .x6 .x6 .x7,
     .LD .x24 .x6 0, .LD .x25 .x6 8,
     .SLTU .x26 .x21 .x25, .XOR .x27 .x21 .x25, .SLTIU .x27 .x27 1,
     .SLTU .x7 .x20 .x24, .AND .x27 .x27 .x7, .OR .x26 .x26 .x27] ++
    whenZero .x26 subtract ++ whenNonzero .x26 choose
  whenZero .x23 (constant .x26 digit ++ [.SLTU .x26 .x22 .x26] ++
    whenZero .x26 readAndCompare)

def decodePositions : Code :=
  constant .x8 positionsBase ++ constant .x22 121 ++
  (List.range 36).flatMap fun slot =>
    [.ADDI .x23 .x0 0] ++ (List.range 15).flatMap (tryDigit (35 - slot) slot)

/-- Disclosed chain values are ordered by position, then by chain index, as in the DAG encoding. -/
def readChainValues : Code :=
  constant .x9 (Riscv.signatureBase.toNat + 32) ++ constant .x18 chainsBase ++
  (List.range 15).flatMap fun position => (List.range 36).flatMap fun chain =>
    [.LD .x26 .x8 (BitVec.ofNat 12 (8 * chain))] ++ constant .x27 position ++
    [.XOR .x26 .x26 .x27] ++
    whenZero .x26 (copy128 .x9 0 .x18 (16 * chain) ++ [.ADDI .x9 .x9 16])

def chainStep (position chain : ℕ) : Code :=
  let body := copy128 .x18 (16 * chain) .x19 0 ++
    constant .x26 (126 + 189 * position + chain) ++ [.SH .x19 .x26 16] ++
    hashScratch 144 ++ copy128 .x19 128 .x18 (16 * chain)
  [.LD .x26 .x8 (BitVec.ofNat 12 (8 * chain))] ++ constant .x27 position ++
  [.SLTU .x26 .x27 .x26] ++ whenZero .x26 body

def chains : Code :=
  (List.range 14).flatMap fun position => (List.range 36).flatMap (chainStep position)

/-- The concatenation puts the last child in the low bits, matching BitVec append. -/
def hashTriple (src dst : Reg) (group tag : ℕ) : Code :=
  copy128 src (16 * (3 * group + 2)) .x19 0 ++
  copy128 src (16 * (3 * group + 1)) .x19 16 ++
  copy128 src (16 * (3 * group)) .x19 32 ++
  constant .x26 tag ++ [.SH .x19 .x26 48] ++ hashScratch 400 ++
  copy128 .x19 128 dst (16 * group)

def groups : Code :=
  constant .x9 groupsBase ++
  (List.range 12).flatMap (fun j => hashTriple .x18 .x9 j (2730 + j)) ++
  constant .x7 (Riscv.signatureBase.toNat + 608) ++
  (List.range 3).flatMap (fun j => copy128 .x7 (16 * j) .x9 (16 * (12 + j)))

def subtrees : Code :=
  constant .x18 subtreesBase ++
  (List.range 5).flatMap (fun l => hashTriple .x9 .x18 l (2779 + l)) ++
  constant .x7 (Riscv.signatureBase.toNat + 656) ++
  copy128 .x7 0 .x18 80 ++ copy128 .x7 16 .x18 96

def rootAndDecision : Code :=
  (List.range 7).flatMap (fun l => copy128 .x18 (16 * l) .x19 (16 * (6 - l))) ++
  constant .x26 2794 ++ [.SH .x19 .x26 112] ++ hashScratch 912 ++
  constant .x7 (Riscv.publicKeyBase.toNat) ++
  [.LD .x26 .x19 128, .LD .x27 .x7 0, .XOR .x26 .x26 .x27,
   .LD .x24 .x19 136, .LD .x25 .x7 8, .XOR .x24 .x24 .x25,
   .OR .x10 .x26 .x24, .SLTIU .x10 .x10 1, .ADDI .x5 .x0 0, .ECALL]

def verifier : Code :=
  indexAndChecks ++ decodePositions ++ readChainValues ++ chains ++ groups ++ subtrees ++ rootAndDecision

/-- Row `n`, column `s`: number of `n` base-15 digits summing to `s`. -/
def tableData : List Riscv.Byte :=
  (List.range 36).flatMap fun n => (Forest.compositionTable 121 n).flatMap fun count =>
    Riscv.bytesOfVector (BitVec.ofNat 128 count)

def image : Riscv.Image := ⟨verifier, tableData⟩

theorem verifier_length : verifier.length = 29697 := by decide +kernel

theorem tableData_length : tableData.length = 70272 := by decide +kernel

set_option maxRecDepth 100000 in
/-- The assembly image uses only admitted instructions and fits the fixed image limits. -/
theorem image_valid : image.Valid := by
  refine ⟨?_, ?_, ?_⟩
  · change verifier.length ≤ 262144
    rw [verifier_length]
    norm_num
  · change tableData.length ≤ 1048576
    rw [tableData_length]
    norm_num
  · have checked : verifier.all Riscv.admittedInstruction = true := by decide +kernel
    exact List.all_eq_true.mp checked

end OptimalOTS.RiscvUpperProgram
