import OptimalOTS.RiscvMachine

/-!
# Shared RV64IM building blocks of the forest verifier

Constants, forward guards, the fixed memory layout, and the verifier's first phase: the index
query `H(nonce ‖ message)` followed by the nibble checks. The index is accepted when its 32
nibbles are at most 14 and sum to `target = 166`; the same pass stores the chain positions
`14 - nibble` for chains 0 to 31 and position 14 for chains 32 to 35.
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

/-- The prefix ends immediately before the index HASH call. -/
def indexPrefix : Code :=
  constant .x11 0 ++ constant .x19 scratchBase ++
  constant .x7 Riscv.signatureBase.toNat ++
  copy128 .x7 0 .x19 0 ++
  constant .x7 Riscv.messageBase.toNat ++
  copy128 .x7 0 .x19 16 ++ copy128 .x7 16 .x19 32 ++
  [.ADDI .x10 .x19 0, .ADDI .x11 .x0 384, .ADDI .x12 .x19 128, .ADDI .x5 .x0 1]

/-- The word holding nibble `k` of the 128-bit index: the low word for `k < 16`. -/
def nibbleReg (k : ℕ) : Reg := if k < 16 then .x20 else .x21

/-- Process nibble `k`: extract it into `x26` (the mask 15 is held in `x24`), add it to the
running sum `x22`, store the chain position `14 - nibble` at slot `k`, and clear the flag `x23`
unless the nibble is at most 14. -/
def nibbleStep (k : ℕ) : Code :=
  (if k % 16 = 0 then [.AND .x26 (nibbleReg k) .x24]
    else [.SRLI .x26 (nibbleReg k) (BitVec.ofNat 6 (4 * (k % 16))), .AND .x26 .x26 .x24]) ++
  [.ADD .x22 .x22 .x26, .SUB .x27 .x7 .x26, .SD .x8 .x27 (BitVec.ofNat 12 (8 * k)),
   .SLTIU .x26 .x26 15, .AND .x23 .x23 .x26]

/-- Load the index words, clear the sum, set the flag, and point at the position array. -/
def nibbleSetup : Code :=
  [.LD .x20 .x19 128, .LD .x21 .x19 136, .ADDI .x22 .x0 0, .ADDI .x23 .x0 1, .ADDI .x7 .x0 14,
   .ADDI .x24 .x0 15, .ADDI .x25 .x0 166] ++ constant .x8 positionsBase

/-- Chains 32 to 35 are disclosed at position 14; then `x26 = 0` exactly when the digit sum is
`target` and every nibble is at most 14. -/
def nibbleFinish : Code :=
  [.SD .x8 .x7 256, .SD .x8 .x7 264, .SD .x8 .x7 272, .SD .x8 .x7 280,
   .XOR .x22 .x22 .x25, .SLTIU .x23 .x23 1, .OR .x26 .x22 .x23]

/-- The complete acceptance test of the index, which also writes the 36 chain positions. -/
def nibbleChecks : Code := nibbleSetup ++ (List.range 32).flatMap nibbleStep ++ nibbleFinish

def indexLengthCheck : Code := constant .x26 5376 ++ [.XOR .x26 .x26 .x13]

def indexChecks : Code :=
  nibbleChecks ++ whenNonzero .x26 reject ++ indexLengthCheck ++ whenNonzero .x26 reject

def indexAndChecks : Code := indexPrefix ++ [.ECALL] ++ indexChecks

end OptimalOTS.RiscvUpperProgram
