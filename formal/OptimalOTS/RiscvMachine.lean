import OptimalOTS.Statement
import RiscvZkvm.Rv64

/-!
# The competition's RISC-V machine

A subset of RV64IM, with the pinned `riscv-zkvm` semantics. Each ordinary instruction,
including HALT, costs one cycle. HASH costs `blockCost paperParams` on its exact
bit-string input. These are the only system calls: the verifier is deterministic given the
oracle's answers. The machine is Harvard-style: the image's code is an instruction list in its
own code space and data memory is separate, so self-modifying code is not expressible. Code and
initial data are finite, fixed parts of the image.
-/

-- The oracle boundary and counted execution follow Derek Sorensen's `xmss-verify-asm` design.

namespace OptimalOTS.Riscv

open RiscvZkvm.Rv64 OracleComp

abbrev Byte := BitVec 8

/-- The first instruction, constant data, public key, message, and signature buffer. -/
def codeBase : Word := 0x1000
def dataBase : Word := 0x200000
def publicKeyBase : Word := 0x400000
def messageBase : Word := 0x400010
def signatureBase : Word := 0x400030
def stackTop : Word := 0x1000000

/-- Call number in `t0`: HALT=0, HASH=1. -/
def hashCall : Word := 1

/-- Only actual instructions of the pinned RV64IM subset; pseudo-instructions must be expanded.
The low bit of a branch or jump immediate is zero in the instruction encoding. -/
def admittedInstruction : Instr → Bool
  | .LI _ _ | .MV _ _ | .NOP | .CSRS _ _ | .EBREAK => false
  | .BEQ _ _ n | .BNE _ _ n | .BLT _ _ n | .BGE _ _ n
  | .BLTU _ _ n | .BGEU _ _ n => n.toNat % 2 == 0
  | .JAL _ n => n.toNat % 2 == 0
  | _ => true

/-- A fixed assembly image: at most 256 Ki instructions and 1 MiB of initial data. -/
structure Image where
  code : List Instr
  data : List Byte

def Image.Valid (image : Image) : Prop :=
  image.code.length ≤ 262144 ∧ image.data.length ≤ 1048576 ∧
    ∀ i ∈ image.code, admittedInstruction i = true

/-- Little-endian bytes; unused high bits of the last byte are zero. -/
def bytesOfBits (bits : List Bool) : List Byte :=
  (List.range ((bits.length + 7) / 8)).map fun j =>
    BitVec.ofNat 8 ((List.range 8).foldl
      (fun n k => n + if bits[j * 8 + k]?.getD false then 2 ^ k else 0) 0)

def bytesOfVector {n : ℕ} (v : BitVec n) : List Byte :=
  (List.range ((n + 7) / 8)).map fun j => v.extractLsb' (8 * j) 8

/-- Raw input layout, with no parsing or scheme-specific preprocessing by the loader.
`a0/a1/a2` point to pk/message/signature; `a3` holds the signature bit length, capped at
5377 to distinguish every oversized input from an admissible one. Only the first 5376
signature bits are loaded. All remaining memory and registers initially contain zero. -/
def initialState (image : Image) (pk : PublicKey paperParams) (m : Message paperParams)
    (signature : List Bool) : MachineState :=
  let blank : MachineState :=
    { regs := fun _ => 0, mem := fun _ => 0, code := loadProgram codeBase image.code,
      pc := codeBase }
  let s := (((blank.writeBytesAsWords dataBase image.data).writeBytesAsWords publicKeyBase
    (bytesOfVector pk)).writeBytesAsWords messageBase (bytesOfVector m)).writeBytesAsWords
    signatureBase (bytesOfBits (signature.take 5376))
  ((((s.setReg .x2 stackTop).setReg .x10 publicKeyBase).setReg .x11 messageBase).setReg
    .x12 signatureBase).setReg .x13 (BitVec.ofNat 64 (min signature.length 5377))

/-- HASH reads `a1` bits at byte pointer `a0`, least significant bit first in each byte. -/
def hashInput (s : MachineState) : Query :=
  let n := (s.getReg .x11).toNat
  ⟨n, ofBits n ((List.range n).map fun i =>
    (s.getByte (s.getReg .x10 + BitVec.ofNat 64 (i / 8))).getLsbD (i % 8))⟩

/-- The hash input and all four output words must fit valid machine memory. -/
def hashArgumentsValid (s : MachineState) : Bool :=
  isValidOutputRange (s.getReg .x10) (((s.getReg .x11).toNat + 7) / 8) &&
    isValidDwordAccess (s.getReg .x12) && isValidDwordAccess (s.getReg .x12 + 8) &&
    isValidDwordAccess (s.getReg .x12 + 16) && isValidDwordAccess (s.getReg .x12 + 24)

/-- Input is read before output is written, so buffers may overlap. -/
def writeHash (s : MachineState) (answer : BitVec 256) : MachineState :=
  (s.writeWords (s.getReg .x12)
    [answer.extractLsb' 0 64, answer.extractLsb' 64 64,
     answer.extractLsb' 128 64, answer.extractLsb' 192 64]).setPC (s.pc + 4)

/-- `none` is a trap or exhausted proof fuel; successful execution returns decision and cost. -/
abbrev Outcome := Option (Bool × ℕ)

def addCycles (n : ℕ) : Outcome → Outcome := Option.map fun result => (result.1, n + result.2)

/-- Execute at most `fuel` instructions. Fuel is a termination witness, distinct from the score.
Every hash uses the competition's existing oracle, with its actual input bit length. -/
def execute : ℕ → MachineState → OracleComp (Spec paperParams) Outcome
  | 0, _ => pure none
  | fuel + 1, s =>
    match s.code s.pc with
    | none => pure none
    | some instruction =>
      if !admittedInstruction instruction then pure none else
      match instruction with
      | .ECALL =>
        if s.getReg .x5 = 0 then
          if s.getReg .x10 = 0 then pure (some (false, 1)) else
          if s.getReg .x10 = 1 then pure (some (true, 1)) else pure none
        else if s.getReg .x5 = hashCall then
          if hashArgumentsValid s then do
            let input := hashInput s
            let answer ← hash paperParams input.2
            addCycles (blockCost paperParams input.1) <$> execute fuel (writeHash s answer)
          else pure none
        else pure none
      | _ => match step s with
        | none => pure none
        | some next => addCycles 1 <$> execute fuel next

end OptimalOTS.Riscv
