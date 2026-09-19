import Submissions.RiscvUpper.Program
import Submissions.RiscvUpper.ForestVerifier

/-!
# Direct RV64IM forest verifier

Each named node owns a 128-byte slot. The program clears that slot, then reads a disclosure
or computes its value. This deliberately simple layout follows the certified graph's exact
node and query order.
-/

namespace OptimalOTS.RiscvUpperProgram.Direct

open RiscvZkvm.Rv64 Forest Forest.Name RiscvUpperForest.ForestVerifier

/-- Each slot fits the largest node, the 912-bit root input. -/
def slotsBase : ℕ := 0x700000

def slotAddress (n : Name) : ℕ := slotsBase + 128 * n.idx

/-- Establish the two Boolean guards in x24 and x25. -/
def guards : Name → Code
  | .src k =>
    if k.val < 36 then
      [.LD .x26 .x8 (BitVec.ofNat 12 (8 * k.val)), .SLTIU .x24 .x26 1,
       .ADDI .x25 .x0 0]
    else [.ADDI .x24 .x0 0, .ADDI .x25 .x0 0]
  | .ci k t | .ch k t =>
    if k.val < 36 then
      [.LD .x26 .x8 (BitVec.ofNat 12 (8 * k.val)), .ADDI .x24 .x0 0] ++
      constant .x27 t.val ++ [.SLTU .x25 .x27 .x26, .SLTIU .x25 .x25 1]
    else [.ADDI .x24 .x0 0, .ADDI .x25 .x0 0]
  | .cv k t =>
    if k.val < 36 then
      [.LD .x26 .x8 (BitVec.ofNat 12 (8 * k.val))] ++ constant .x27 (t.val + 1) ++
      [.XOR .x24 .x26 .x27, .SLTIU .x24 .x24 1] ++ constant .x27 t.val ++
      [.SLTU .x25 .x27 .x26, .SLTIU .x25 .x25 1]
    else [.ADDI .x24 .x0 0, .ADDI .x25 .x0 0]
  | .gc j | .gh j => constant .x24 0 ++ constant .x25 (decide (j.val < 12)).toNat
  | .gv j => constant .x24 (decide (12 ≤ j.val ∧ j.val < 15)).toNat ++
      constant .x25 (decide (j.val < 12)).toNat
  | .ec l | .eh l => constant .x24 0 ++ constant .x25 (decide (l.val < 5)).toNat
  | .ev l => constant .x24 (decide (5 ≤ l.val)).toNat ++
      constant .x25 (decide (l.val < 5)).toNat
  | .rc | .rh => [.ADDI .x24 .x0 0, .ADDI .x25 .x0 1]

/-- Clear the entire destination slot, including padding of tagged inputs. -/
def clearSlot : Code :=
  (List.range 16).map fun j => .SD .x18 .x0 (BitVec.ofNat 12 (8 * j))

/-- Copy one child's low 128 bits into the destination slot. -/
def copyChild (child : Name) (offset : ℕ) : Code :=
  constant .x7 (slotAddress child) ++ copy128 .x7 0 .x18 offset

def writeTag (tag : BitVec 16) (offset : ℕ) : Code :=
  constant .x26 tag.toNat ++ [.SH .x18 .x26 (BitVec.ofNat 12 offset)]

/-- Compile one of the forest's six operation forms. -/
def operation : NodeOp → Code
  | .zero => []
  | .copy source => copyChild source 0
  | .tagged1 tag source => copyChild source 0 ++ writeTag tag 16
  | .tagged3 tag a b c =>
      copyChild c 0 ++ copyChild b 16 ++ copyChild a 32 ++ writeTag tag 48
  | .tagged7 tag children =>
      (List.finRange 7).reverse.flatMap (fun l => copyChild (children l) (16 * (6 - l.val))) ++
      writeTag tag 112
  | .hash source =>
      constant .x10 (slotAddress source) ++ constant .x11 source.len ++
      [.ADDI .x12 .x18 0, .ADDI .x5 .x0 1, .ECALL]

/-- Reading a disclosure advances the byte cursor by one word. -/
def readDisclosure : Code := copy128 .x9 0 .x18 0 ++ [.ADDI .x9 .x9 16]

def nodeCode (n : Name) : Code :=
  constant .x18 (slotAddress n) ++ clearSlot ++ guards n ++
  whenNonzero .x24 readDisclosure ++ whenNonzero .x25 (operation (nodeOp n))

def reconstruction : Code :=
  constant .x9 (Riscv.signatureBase.toNat + 16) ++ order.flatMap nodeCode

/-- Compare the root hash's low 128 bits with the public key and halt. -/
def decision : Code :=
  constant .x18 (slotAddress rh) ++ constant .x7 Riscv.publicKeyBase.toNat ++
  [.LD .x26 .x18 0, .LD .x27 .x7 0, .XOR .x26 .x26 .x27,
   .LD .x24 .x18 8, .LD .x25 .x7 8, .XOR .x24 .x24 .x25,
   .OR .x10 .x26 .x24, .SLTIU .x10 .x10 1, .ADDI .x5 .x0 0, .ECALL]

/-- The fixed slot arena lies in admitted memory. -/
theorem slotAddress_bounds (n : Name) :
    0x700000 ≤ slotAddress n ∧ slotAddress n + 128 ≤ 0x1000000 := by
  have h := n.idx_lt
  simp only [N] at h
  unfold slotAddress slotsBase
  omega

theorem slotAddress_aligned (n : Name) : slotAddress n % 128 = 0 := by
  simp [slotAddress, slotsBase, Nat.add_mod]

theorem slotAddress_injective : Function.Injective slotAddress := by
  intro a b h
  apply Name.idx_injective
  unfold slotAddress at h
  omega

end OptimalOTS.RiscvUpperProgram.Direct
