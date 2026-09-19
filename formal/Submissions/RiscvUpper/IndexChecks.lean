import Submissions.RiscvUpper.IndexInput
import Submissions.RiscvUpper.HashOutput

/-!
# The nibble checks

After the index HASH, the verifier loads the 128-bit index into `x20`/`x21`, sweeps its 32
nibbles (adding each to the sum in `x22`, clearing the flag `x23` when a nibble exceeds 14, and
storing the chain position `14 - nibble`), stores position 14 for chains 32 to 35, and rejects
unless the sum is `target` and the flag is set. A final check rejects wrong signature lengths.
-/

namespace OptimalOTS.RiscvUpperProgram

open RiscvZkvm.Rv64

set_option maxRecDepth 100000

/-! ## The index and its nibbles -/

def joinWords (lo hi : Word) : BitVec 128 := hi ++ lo

theorem joinWords_toNat (lo hi : Word) :
    (joinWords lo hi).toNat = hi.toNat * 2 ^ 64 + lo.toNat := by
  rw [joinWords, BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt lo.isLt, Nat.shiftLeft_eq]

/-- The index held in the two index registers. -/
def rankOf (s : MachineState) : ℕ := (joinWords (s.getReg .x20) (s.getReg .x21)).toNat

theorem answer_low128 (answer : BitVec 256) :
    joinWords (answer.extractLsb' 0 64) (answer.extractLsb' 64 64) = answer.setWidth 128 := by
  rw [joinWords, BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by decide)]
  ext i hi
  simp

theorem nibble_word (w : Word) (m : ℕ) :
    ((w >>> (4 * m)) &&& (15 : Word)).toNat = nibble w.toNat m := by
  rw [BitVec.toNat_and, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have h := Nat.and_two_pow_sub_one_eq_mod (w.toNat / 2 ^ (4 * m)) 4
  norm_num at h
  rw [show (15 : Word).toNat = 15 from rfl, h, nibble, pow_mul]
  norm_num

theorem nibble_word_zero (w : Word) : (w &&& (15 : Word)).toNat = nibble w.toNat 0 := by
  have h := nibble_word w 0
  rwa [Nat.mul_zero, BitVec.ushiftRight_zero] at h

theorem nibble_joinWords_lo (lo hi : Word) (m : ℕ) (hm : m < 16) :
    nibble (joinWords lo hi).toNat m = nibble lo.toNat m := by
  rw [joinWords_toNat, nibble, nibble]
  have split : (16 : ℕ) ^ m * (16 * 16 ^ (15 - m)) = 2 ^ 64 := by
    rw [← pow_succ', ← pow_add, show m + (15 - m + 1) = 16 by omega]
    norm_num
  have e : hi.toNat * 2 ^ 64 + lo.toNat =
      lo.toNat + 16 ^ m * (16 * (hi.toNat * 16 ^ (15 - m))) := by
    rw [← split]
    ring
  rw [e, Nat.add_mul_div_left _ _ (by positivity), Nat.add_mul_mod_self_left]

theorem nibble_joinWords_hi (lo hi : Word) (m : ℕ) (hm : 16 ≤ m) :
    nibble (joinWords lo hi).toNat m = nibble hi.toNat (m - 16) := by
  rw [joinWords_toNat, nibble, nibble]
  have e : (16 : ℕ) ^ m = 2 ^ 64 * 16 ^ (m - 16) := by
    rw [show (2 : ℕ) ^ 64 = 16 ^ 16 by norm_num, ← pow_add, Nat.add_sub_cancel' hm]
  rw [e, ← Nat.div_div_eq_div_mul, Nat.mul_comm hi.toNat, Nat.mul_add_div (by positivity),
    Nat.div_eq_of_lt lo.isLt, Nat.add_zero]

/-- The nibble extracted by step `k` of the sweep. -/
def stepNibble (s : MachineState) (k : ℕ) : Word :=
  if k % 16 = 0 then s.getReg (nibbleReg k) &&& s.getReg .x24
  else (s.getReg (nibbleReg k) >>> (BitVec.ofNat 6 (4 * (k % 16))).toNat) &&& s.getReg .x24

theorem stepNibble_toNat (s : MachineState) (k : ℕ) (hk : k < 32) (mask : s.getReg .x24 = 15) :
    (stepNibble s k).toNat = nibble (rankOf s) k := by
  have shamt : (BitVec.ofNat 6 (4 * (k % 16))).toNat = 4 * (k % 16) := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    have := Nat.mod_lt k (by norm_num : 0 < 16)
    omega
  unfold stepNibble rankOf nibbleReg
  rw [mask]
  by_cases hlo : k < 16
  · rw [if_pos hlo, nibble_joinWords_lo _ _ k hlo]
    have hmod : k % 16 = k := Nat.mod_eq_of_lt hlo
    by_cases h0 : k % 16 = 0
    · rw [if_pos h0, nibble_word_zero, show k = 0 by omega]
    · rw [if_neg h0, shamt, nibble_word, hmod]
  · rw [if_neg hlo, nibble_joinWords_hi _ _ k (by omega)]
    have hmod : k % 16 = k - 16 := by omega
    by_cases h0 : k % 16 = 0
    · rw [if_pos h0, nibble_word_zero, show k - 16 = 0 by omega]
    · rw [if_neg h0, shamt, nibble_word, hmod]

/-! ## The nibble sum and flag -/

/-- The digit sum of the first `n` nibbles of `i`. -/
def nibbleSum (i n : ℕ) : ℕ := ∑ k ∈ Finset.range n, nibble i k

/-- The first `n` nibbles of `i` are at most 14. -/
def NibbleOk (i n : ℕ) : Prop := ∀ k ∈ Finset.range n, nibble i k ≤ 14

instance (i n : ℕ) : Decidable (NibbleOk i n) := by unfold NibbleOk; infer_instance

theorem accepted_iff (i : ℕ) : Accepted i ↔ NibbleOk i 32 ∧ nibbleSum i 32 = target := Iff.rfl

theorem nibbleSum_succ (i n : ℕ) : nibbleSum i (n + 1) = nibbleSum i n + nibble i n :=
  Finset.sum_range_succ _ _

theorem nibbleOk_succ (i n : ℕ) : NibbleOk i (n + 1) ↔ NibbleOk i n ∧ nibble i n ≤ 14 := by
  unfold NibbleOk
  simp only [Finset.mem_range]
  constructor
  · intro h
    exact ⟨fun k hk => h k (by omega), h n (by omega)⟩
  · rintro ⟨h, hn⟩ k hk
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
    · exact h k hk
    · exact hn

theorem nibbleSum_le (i n : ℕ) : nibbleSum i n ≤ 15 * n := by
  unfold nibbleSum
  calc ∑ k ∈ Finset.range n, nibble i k ≤ ∑ _k ∈ Finset.range n, 15 :=
        Finset.sum_le_sum fun k _ => Nat.le_of_lt_succ (nibble_lt i k)
    _ = 15 * n := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul, Nat.mul_comm]

/-! ## The position array -/

def positionAddr (k : ℕ) : Word := BitVec.ofNat 64 positionsBase + BitVec.ofNat 64 (8 * k)

theorem positionAddr_toNat (k : ℕ) (hk : k < 36) : (positionAddr k).toNat = positionsBase + 8 * k := by
  simp only [positionAddr, BitVec.toNat_add, BitVec.toNat_ofNat, positionsBase]
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

theorem positionAddr_injective {j k : ℕ} (hj : j < 36) (hk : k < 36)
    (h : positionAddr j = positionAddr k) : j = k := by
  have := congrArg BitVec.toNat h
  rw [positionAddr_toNat j hj, positionAddr_toNat k hk] at this
  omega

theorem position_store_valid (k : ℕ) (hk : k < 36) :
    isValidDwordAccess (positionAddr k) = true := by
  simp only [isValidDwordAccess, isValidMemAddr, isAligned8, positionAddr_toNat k hk,
    Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq]
  refine ⟨Or.inl (Or.inl ⟨?_, ?_⟩), ?_⟩ <;> norm_num [MEM_START, MEM_END, positionsBase] <;> omega

theorem position_offset (k : ℕ) (hk : k < 36) :
    BitVec.ofNat 64 positionsBase + signExtend12 (BitVec.ofNat 12 (8 * k)) = positionAddr k := by
  rw [signExtend12_nonnegative _ (by omega)]
  rfl

end OptimalOTS.RiscvUpperProgram

namespace OptimalOTS.RiscvUpperProgram

open RiscvZkvm.Rv64

set_option maxRecDepth 100000

/-! ## One sweep step -/

theorem nibbleStep_length (k : ℕ) : (nibbleStep k).length = if k % 16 = 0 then 6 else 7 := by
  unfold nibbleStep
  split_ifs <;> rfl

/-- The registers and memory after one nibble step. -/
theorem nibbleStep_effect (t : MachineState) (k : ℕ) :
    ((nibbleStep k).foldl execInstrBr t).getReg .x22 = t.getReg .x22 + stepNibble t k ∧
    ((nibbleStep k).foldl execInstrBr t).getReg .x23 =
      t.getReg .x23 &&& (if BitVec.ult (stepNibble t k) (signExtend12 15) then 1 else 0) ∧
    (∀ r, r ≠ .x22 → r ≠ .x23 → r ≠ .x26 → r ≠ .x27 →
      ((nibbleStep k).foldl execInstrBr t).getReg r = t.getReg r) ∧
    ((nibbleStep k).foldl execInstrBr t).mem =
      (t.setMem (t.getReg .x8 + signExtend12 (BitVec.ofNat 12 (8 * k)))
        (t.getReg .x7 - stepNibble t k)).mem ∧
    ((nibbleStep k).foldl execInstrBr t).code = t.code := by
  have regs : ∀ r, r ≠ .x22 → r ≠ .x23 → r ≠ .x26 → r ≠ .x27 →
      ((nibbleStep k).foldl execInstrBr t).getReg r = t.getReg r := by
    intro r h22 h23 h26 h27
    unfold nibbleStep
    by_cases h0 : k % 16 = 0
    · rw [if_pos h0]
      cases r <;> first | exact absurd rfl ‹_› | rfl
    · rw [if_neg h0]
      cases r <;> first | exact absurd rfl ‹_› | rfl
  refine ⟨?_, ?_, regs, ?_, ?_⟩
  all_goals (unfold nibbleStep; try unfold stepNibble)
  all_goals by_cases h0 : k % 16 = 0
  all_goals simp only [h0, if_true, if_false]
  all_goals rfl

/-- Every step is straight-line code whose store lands in the position array. -/
theorem nibbleStep_ready (t : MachineState) (k : ℕ) (hk : k < 32)
    (x8 : t.getReg .x8 = BitVec.ofNat 64 positionsBase) :
    Riscv.LinearReady t (nibbleStep k) := by
  have valid := position_store_valid k (by omega)
  rw [← position_offset k (by omega), ← x8] at valid
  unfold nibbleStep
  by_cases h0 : k % 16 = 0
  · rw [if_pos h0]
    simp only [List.cons_append, List.nil_append, Riscv.LinearReady, Riscv.linearInstruction,
      Riscv.memoryReady, true_and, and_true]
    exact valid
  · rw [if_neg h0]
    simp only [List.cons_append, List.nil_append, Riscv.LinearReady, Riscv.linearInstruction,
      Riscv.memoryReady, true_and, and_true]
    exact valid

/-! ## The sweep -/

/-- The nibble sweep after `n` steps from the state `s` that follows the setup. -/
structure Swept (s t : MachineState) (i n : ℕ) : Prop where
  x20 : t.getReg .x20 = s.getReg .x20
  x21 : t.getReg .x21 = s.getReg .x21
  x7 : t.getReg .x7 = s.getReg .x7
  x8 : t.getReg .x8 = s.getReg .x8
  x13 : t.getReg .x13 = s.getReg .x13
  x19 : t.getReg .x19 = s.getReg .x19
  x24 : t.getReg .x24 = s.getReg .x24
  x25 : t.getReg .x25 = s.getReg .x25
  x22 : t.getReg .x22 = BitVec.ofNat 64 (nibbleSum i n)
  x23 : t.getReg .x23 = if NibbleOk i n then (1 : Word) else 0
  positions : ∀ k, k < n → t.getMem (positionAddr k) = (14 : Word) - BitVec.ofNat 64 (nibble i k)
  frame : ∀ addr, (∀ k, k < n → addr ≠ positionAddr k) → t.getMem addr = s.getMem addr
  code : t.code = s.code

theorem Swept.zero (s : MachineState) (i : ℕ) (x22 : s.getReg .x22 = 0)
    (x23 : s.getReg .x23 = 1) : Swept s s i 0 where
  x20 := rfl
  x21 := rfl
  x7 := rfl
  x8 := rfl
  x13 := rfl
  x19 := rfl
  x24 := rfl
  x25 := rfl
  x22 := by rw [x22]; rfl
  x23 := by
    have h0 : NibbleOk i 0 := fun k hk => by simp at hk
    rw [x23, if_pos h0]
  positions := fun k hk => by omega
  frame := fun _ _ => rfl
  code := rfl

theorem ult_fifteen (nib : Word) : BitVec.ult nib (signExtend12 15) ↔ nib.toNat ≤ 14 := by
  have h15 : signExtend12 15 = (15 : Word) := by decide
  rw [h15, BitVec.ult_iff_lt, BitVec.lt_def]
  show nib.toNat < (15 : Word).toNat ↔ nib.toNat ≤ 14
  rw [show (15 : Word).toNat = 15 from rfl]
  omega

theorem flag_and (p q : Prop) [Decidable p] [Decidable q] :
    (if p then (1 : Word) else 0) &&& (if q then (1 : Word) else 0) =
      if p ∧ q then (1 : Word) else 0 := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]

theorem Swept.step (s t : MachineState) (i n : ℕ) (hn : n < 32)
    (hi : i = rankOf s) (x7 : s.getReg .x7 = 14) (x8 : s.getReg .x8 = BitVec.ofNat 64 positionsBase)
    (x24 : s.getReg .x24 = 15)
    (h : Swept s t i n) : Swept s ((nibbleStep n).foldl execInstrBr t) i (n + 1) := by
  obtain ⟨e22, e23, others, mem, code⟩ := nibbleStep_effect t n
  have rank : rankOf t = i := by rw [hi, rankOf, rankOf, h.x20, h.x21]
  have nibVal : (stepNibble t n).toNat = nibble i n := by
    rw [stepNibble_toNat t n hn (by rw [h.x24, x24]), rank]
  have nibSmall : stepNibble t n = BitVec.ofNat 64 (nibble i n) := by
    rw [← nibVal, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have addr : t.getReg .x8 + signExtend12 (BitVec.ofNat 12 (8 * n)) = positionAddr n := by
    rw [h.x8, x8, position_offset n (by omega)]
  have flag : (BitVec.ult (stepNibble t n) (signExtend12 15) = true) ↔ nibble i n ≤ 14 := by
    rw [ult_fifteen, nibVal]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [others .x20 (by decide) (by decide) (by decide) (by decide), h.x20]
  · rw [others .x21 (by decide) (by decide) (by decide) (by decide), h.x21]
  · rw [others .x7 (by decide) (by decide) (by decide) (by decide), h.x7]
  · rw [others .x8 (by decide) (by decide) (by decide) (by decide), h.x8]
  · rw [others .x13 (by decide) (by decide) (by decide) (by decide), h.x13]
  · rw [others .x19 (by decide) (by decide) (by decide) (by decide), h.x19]
  · rw [others .x24 (by decide) (by decide) (by decide) (by decide), h.x24]
  · rw [others .x25 (by decide) (by decide) (by decide) (by decide), h.x25]
  · rw [e22, h.x22, nibSmall, nibbleSum_succ, BitVec.ofNat_add]
  · rw [e23, h.x23]
    simp only [flag]
    rw [flag_and]
    simp only [nibbleOk_succ]
  · intro k hk
    change ((nibbleStep n).foldl execInstrBr t).mem (positionAddr k) = _
    rw [mem]
    by_cases hkn : k = n
    · subst hkn
      change (t.setMem _ _).getMem (positionAddr k) = _
      rw [addr, MachineState.getMem_setMem_eq, h.x7, x7, nibSmall]
    · change (t.setMem _ _).getMem (positionAddr k) = _
      rw [addr, MachineState.getMem_setMem_ne
        (fun e => hkn (positionAddr_injective (by omega) (by omega) e))]
      exact h.positions k (by omega)
  · intro a ha
    change ((nibbleStep n).foldl execInstrBr t).mem a = _
    rw [mem]
    change (t.setMem _ _).getMem a = _
    rw [addr, MachineState.getMem_setMem_ne (ha n (by omega))]
    exact h.frame a (fun k hk => ha k (by omega))
  · rw [code, h.code]

/-- The whole sweep from the post-setup state, together with its readiness. -/
theorem sweep_effect (s : MachineState) (i : ℕ) (hi : i = rankOf s)
    (x7 : s.getReg .x7 = 14) (x8 : s.getReg .x8 = BitVec.ofNat 64 positionsBase)
    (x24 : s.getReg .x24 = 15) (x22 : s.getReg .x22 = 0) (x23 : s.getReg .x23 = 1) :
    ∀ n, n ≤ 32 →
      Swept s (((List.range n).flatMap nibbleStep).foldl execInstrBr s) i n ∧
      Riscv.LinearReady s ((List.range n).flatMap nibbleStep) := by
  intro n
  induction n with
  | zero => intro _; exact ⟨Swept.zero s i x22 x23, trivial⟩
  | succ n ih =>
    intro hn
    obtain ⟨swept, ready⟩ := ih (by omega)
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, List.foldl_append]
    refine ⟨Swept.step s _ i n (by omega) hi x7 x8 x24 swept, ?_⟩
    exact ready.append (nibbleStep_ready _ n (by omega) (by rw [swept.x8, x8]))

end OptimalOTS.RiscvUpperProgram

namespace OptimalOTS.RiscvUpperProgram

open RiscvZkvm.Rv64

set_option maxRecDepth 100000

/-! ## Setup -/

theorem nibbleSetup_length : nibbleSetup.length = 9 := by decide +kernel

theorem nibbleSetup_ready (s : MachineState) (scratch : s.getReg .x19 = BitVec.ofNat 64 scratchBase) :
    Riscv.LinearReady s nibbleSetup := by
  simp [nibbleSetup, constant, positionsBase, Riscv.LinearReady, Riscv.linearInstruction,
    Riscv.memoryReady, execInstrBr, scratch, MachineState.getReg_setReg_ne, scratchBase,
    signExtend12, MEM_START, MEM_END]

/-- The state after the setup. -/
def setupState (s : MachineState) : MachineState := nibbleSetup.foldl execInstrBr s

/-- The index words loaded by the setup. -/
def indexOf (s : MachineState) : ℕ :=
  (joinWords (s.getMem (s.getReg .x19 + 128)) (s.getMem (s.getReg .x19 + 136))).toNat

theorem setupState_x20 (s : MachineState) : (setupState s).getReg .x20 = s.getMem (s.getReg .x19 + 128) := by
  show s.getMem (s.getReg .x19 + signExtend12 128) = _
  rw [show signExtend12 128 = (128 : Word) by decide]

theorem setupState_x21 (s : MachineState) : (setupState s).getReg .x21 = s.getMem (s.getReg .x19 + 136) := by
  show s.getMem (s.getReg .x19 + signExtend12 136) = _
  rw [show signExtend12 136 = (136 : Word) by decide]

theorem setupState_rank (s : MachineState) : rankOf (setupState s) = indexOf s := by
  rw [rankOf, indexOf, setupState_x20, setupState_x21]

theorem setupState_regs (s : MachineState) :
    (setupState s).getReg .x22 = 0 ∧ (setupState s).getReg .x23 = 1 ∧
    (setupState s).getReg .x7 = 14 ∧ (setupState s).getReg .x24 = 15 ∧
    (setupState s).getReg .x25 = 166 ∧
    (setupState s).getReg .x8 = BitVec.ofNat 64 positionsBase ∧
    (setupState s).getReg .x13 = s.getReg .x13 ∧ (setupState s).getReg .x19 = s.getReg .x19 ∧
    (setupState s).mem = s.mem ∧ (setupState s).code = s.code := by
  have baseLiteral : literalValue positionsBase = BitVec.ofNat 64 positionsBase := by decide +kernel
  have e : setupState s = (constant .x8 positionsBase).foldl execInstrBr
      (([.LD .x20 .x19 128, .LD .x21 .x19 136, .ADDI .x22 .x0 0, .ADDI .x23 .x0 1,
        .ADDI .x7 .x0 14, .ADDI .x24 .x0 15, .ADDI .x25 .x0 166] : Code).foldl execInstrBr s) := rfl
  rw [e]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [constant_preserves _ _ _ _ (by decide)]
    show (0 : Word) + signExtend12 0 = 0
    decide
  · rw [constant_preserves _ _ _ _ (by decide)]
    show (0 : Word) + signExtend12 1 = 1
    decide
  · rw [constant_preserves _ _ _ _ (by decide)]
    show (0 : Word) + signExtend12 14 = 14
    decide
  · rw [constant_preserves _ _ _ _ (by decide)]
    show (0 : Word) + signExtend12 15 = 15
    decide
  · rw [constant_preserves _ _ _ _ (by decide)]
    show (0 : Word) + signExtend12 166 = 166
    decide
  · rw [constant_value _ _ _ (by decide), baseLiteral]
  · rw [constant_preserves _ _ _ _ (by decide)]
    rfl
  · rw [constant_preserves _ _ _ _ (by decide)]
    rfl
  · rw [constant_mem]
    rfl
  · rw [Riscv.fold_code]
    rfl

/-! ## Finish -/

theorem nibbleFinish_length : nibbleFinish.length = 7 := rfl

theorem finish_addr_32 : BitVec.ofNat 64 positionsBase + signExtend12 256 = positionAddr 32 := by decide
theorem finish_addr_33 : BitVec.ofNat 64 positionsBase + signExtend12 264 = positionAddr 33 := by decide
theorem finish_addr_34 : BitVec.ofNat 64 positionsBase + signExtend12 272 = positionAddr 34 := by decide
theorem finish_addr_35 : BitVec.ofNat 64 positionsBase + signExtend12 280 = positionAddr 35 := by decide

theorem nibbleFinish_ready (t : MachineState) (x8 : t.getReg .x8 = BitVec.ofNat 64 positionsBase) :
    Riscv.LinearReady t nibbleFinish := by
  have r : ∀ (u : MachineState) (a v : Word), (u.setMem a v).getReg .x8 = u.getReg .x8 :=
    fun u a v => rfl
  simp only [nibbleFinish, Riscv.LinearReady, Riscv.linearInstruction, Riscv.memoryReady, true_and,
    and_true, execInstrBr, MachineState.getReg_setPC, r, x8, finish_addr_32, finish_addr_33,
    finish_addr_34, finish_addr_35]
  exact ⟨position_store_valid 32 (by omega), position_store_valid 33 (by omega),
    position_store_valid 34 (by omega), position_store_valid 35 (by omega)⟩

/-- The state after the finish. -/
theorem nibbleFinish_effect (t : MachineState) (x8 : t.getReg .x8 = BitVec.ofNat 64 positionsBase) :
    (nibbleFinish.foldl execInstrBr t).getReg .x26 =
      (t.getReg .x22 ^^^ t.getReg .x25) |||
        (if BitVec.ult (t.getReg .x23) (signExtend12 1) then 1 else 0) ∧
    (∀ r, r ≠ .x22 → r ≠ .x23 → r ≠ .x26 →
      (nibbleFinish.foldl execInstrBr t).getReg r = t.getReg r) ∧
    (nibbleFinish.foldl execInstrBr t).mem =
      ((((t.setMem (positionAddr 32) (t.getReg .x7)).setMem (positionAddr 33) (t.getReg .x7)).setMem
        (positionAddr 34) (t.getReg .x7)).setMem (positionAddr 35) (t.getReg .x7)).mem ∧
    (nibbleFinish.foldl execInstrBr t).code = t.code := by
  refine ⟨rfl, ?_, ?_, rfl⟩
  · intro r h22 h23 h26
    cases r <;> first | exact absurd rfl ‹_› | rfl
  · show ((((t.setMem (t.getReg .x8 + signExtend12 256) (t.getReg .x7)).setMem
      (t.getReg .x8 + signExtend12 264) (t.getReg .x7)).setMem
      (t.getReg .x8 + signExtend12 272) (t.getReg .x7)).setMem
      (t.getReg .x8 + signExtend12 280) (t.getReg .x7)).mem = _
    rw [x8, finish_addr_32, finish_addr_33, finish_addr_34, finish_addr_35]

/-! ## The complete check -/

theorem nibbleChecks_length : nibbleChecks.length = 238 := by decide +kernel

theorem nibbleChecks_split :
    nibbleChecks = nibbleSetup ++ ((List.range 32).flatMap nibbleStep ++ nibbleFinish) := by
  simp only [nibbleChecks, List.append_assoc]

/-- The sweep state after setup and all 32 steps. -/
theorem sweptState (s : MachineState) :
    Swept (setupState s) (((List.range 32).flatMap nibbleStep).foldl execInstrBr (setupState s))
      (indexOf s) 32 ∧
    Riscv.LinearReady (setupState s) ((List.range 32).flatMap nibbleStep) := by
  obtain ⟨x22, x23, x7, x24, _, x8, _, _, _, _⟩ := setupState_regs s
  exact sweep_effect (setupState s) (indexOf s) (setupState_rank s).symm x7 x8 x24 x22 x23 32 le_rfl

theorem nibbleChecks_ready (s : MachineState) (scratch : s.getReg .x19 = BitVec.ofNat 64 scratchBase) :
    Riscv.LinearReady s nibbleChecks := by
  obtain ⟨swept, ready⟩ := sweptState s
  obtain ⟨_, _, _, _, _, x8, _, _, _, _⟩ := setupState_regs s
  rw [nibbleChecks_split]
  refine (nibbleSetup_ready s scratch).append (ready.append ?_)
  exact nibbleFinish_ready _ (by rw [swept.x8, x8])

theorem accept_test (sum flag : Word) (i : ℕ) (hsum : sum = BitVec.ofNat 64 (nibbleSum i 32))
    (hflag : flag = if NibbleOk i 32 then (1 : Word) else 0) :
    ((sum ^^^ (166 : Word)) ||| (if BitVec.ult flag (signExtend12 1) then (1 : Word) else 0)) = 0#64 ↔
      Accepted i := by
  rw [BitVec.or_eq_zero_iff, BitVec.xor_eq_zero_iff, accepted_iff, hsum, hflag]
  have h1 : signExtend12 1 = (1 : Word) := by decide
  rw [h1]
  have bound := nibbleSum_le i 32
  constructor
  · rintro ⟨hs, hf⟩
    refine ⟨?_, ?_⟩
    · by_contra hok
      rw [if_neg hok] at hf
      exact absurd hf (by decide)
    · have := congrArg BitVec.toNat hs
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
      exact this
  · rintro ⟨hok, hs⟩
    refine ⟨?_, ?_⟩
    · rw [hs]; rfl
    · rw [if_pos hok]; decide

/-- The registers and memory after the complete check. -/
theorem nibbleChecks_effect (s : MachineState) :
    let u := nibbleChecks.foldl execInstrBr s
    (u.getReg .x26 = 0#64 ↔ Accepted (indexOf s)) ∧
    u.getReg .x8 = BitVec.ofNat 64 positionsBase ∧ u.getReg .x13 = s.getReg .x13 ∧
    rankOf u = indexOf s ∧
    (∀ k, k < 32 → u.getMem (positionAddr k) = (14 : Word) - BitVec.ofNat 64 (nibble (indexOf s) k)) ∧
    (∀ k, 32 ≤ k → k < 36 → u.getMem (positionAddr k) = 14) ∧
    (∀ addr, (∀ k, k < 36 → addr ≠ positionAddr k) → u.getMem addr = s.getMem addr) ∧
    u.code = s.code := by
  intro u
  obtain ⟨swept, _⟩ := sweptState s
  obtain ⟨x22, x23, x7, x24, x25, x8, x13, x19, mem, code⟩ := setupState_regs s
  set t := ((List.range 32).flatMap nibbleStep).foldl execInstrBr (setupState s) with ht
  have tx8 : t.getReg .x8 = BitVec.ofNat 64 positionsBase := by rw [swept.x8, x8]
  obtain ⟨f26, fregs, fmem, fcode⟩ := nibbleFinish_effect t tx8
  have hu : u = nibbleFinish.foldl execInstrBr t := by
    show nibbleChecks.foldl execInstrBr s =
      nibbleFinish.foldl execInstrBr
        (((List.range 32).flatMap nibbleStep).foldl execInstrBr (setupState s))
    rw [nibbleChecks_split, List.foldl_append, List.foldl_append]
    rfl
  rw [hu]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [f26, swept.x25, x25, swept.x22, swept.x23]
    exact accept_test _ _ _ rfl rfl
  · rw [fregs .x8 (by decide) (by decide) (by decide), tx8]
  · rw [fregs .x13 (by decide) (by decide) (by decide), swept.x13, x13]
  · rw [rankOf, fregs .x20 (by decide) (by decide) (by decide), fregs .x21 (by decide) (by decide) (by decide),
      swept.x20, swept.x21, ← rankOf, setupState_rank]
  · intro k hk
    change (nibbleFinish.foldl execInstrBr t).mem (positionAddr k) = _
    rw [fmem]
    change ((((t.setMem _ _).setMem _ _).setMem _ _).setMem _ _).getMem (positionAddr k) = _
    rw [MachineState.getMem_setMem_ne (fun e => by have := positionAddr_injective (by omega) (by omega) e; omega),
      MachineState.getMem_setMem_ne (fun e => by have := positionAddr_injective (by omega) (by omega) e; omega),
      MachineState.getMem_setMem_ne (fun e => by have := positionAddr_injective (by omega) (by omega) e; omega),
      MachineState.getMem_setMem_ne (fun e => by have := positionAddr_injective (by omega) (by omega) e; omega)]
    exact swept.positions k hk
  · intro k hk hk'
    change (nibbleFinish.foldl execInstrBr t).mem (positionAddr k) = _
    rw [fmem]
    change ((((t.setMem _ _).setMem _ _).setMem _ _).setMem _ _).getMem (positionAddr k) = _
    have v : t.getReg .x7 = 14 := by rw [swept.x7, x7]
    rcases (by omega : k = 32 ∨ k = 33 ∨ k = 34 ∨ k = 35) with rfl | rfl | rfl | rfl
    · rw [MachineState.getMem_setMem_ne (by decide), MachineState.getMem_setMem_ne (by decide),
        MachineState.getMem_setMem_ne (by decide), MachineState.getMem_setMem_eq, v]
    · rw [MachineState.getMem_setMem_ne (by decide), MachineState.getMem_setMem_ne (by decide),
        MachineState.getMem_setMem_eq, v]
    · rw [MachineState.getMem_setMem_ne (by decide), MachineState.getMem_setMem_eq, v]
    · rw [MachineState.getMem_setMem_eq, v]
  · intro a ha
    change (nibbleFinish.foldl execInstrBr t).mem a = _
    rw [fmem]
    change ((((t.setMem _ _).setMem _ _).setMem _ _).setMem _ _).getMem a = _
    rw [MachineState.getMem_setMem_ne (ha 35 (by omega)), MachineState.getMem_setMem_ne (ha 34 (by omega)),
      MachineState.getMem_setMem_ne (ha 33 (by omega)), MachineState.getMem_setMem_ne (ha 32 (by omega))]
    rw [swept.frame a (fun k hk => ha k (by omega))]
    exact congrFun mem a
  · rw [fcode, swept.code, code]

end OptimalOTS.RiscvUpperProgram

namespace OptimalOTS.RiscvUpperProgram

open RiscvZkvm.Rv64

set_option maxRecDepth 100000

/-! ## The checked state -/

theorem indexAndChecks_split : indexAndChecks = indexPrefix ++ [.ECALL] ++ indexChecks := rfl

theorem indexChecks_length : indexChecks.length = 249 := by decide +kernel

theorem indexAndChecks_length : indexAndChecks.length = 273 := by decide +kernel

theorem indexLengthCheck_length : indexLengthCheck.length = 3 := rfl

def skipReject (s : MachineState) : MachineState := s.setPC (s.pc + 16)

/-- The state entering the chain phase: both rejections skipped. -/
def checkedIndexState (s : MachineState) : MachineState :=
  skipReject (indexLengthCheck.foldl execInstrBr (skipReject (nibbleChecks.foldl execInstrBr s)))

theorem indexLengthCheck_ready (s : MachineState) : Riscv.LinearReady s indexLengthCheck := by
  simp [indexLengthCheck, constant, Riscv.LinearReady, Riscv.linearInstruction, Riscv.memoryReady]

theorem indexLengthCheck_test (s : MachineState) :
    (indexLengthCheck.foldl execInstrBr s).getReg .x26 = 5376 ^^^ s.getReg .x13 := rfl

theorem indexLengthCheck_preserves (s : MachineState) (r : Reg) (h : r ≠ .x26) :
    (indexLengthCheck.foldl execInstrBr s).getReg r = s.getReg r := by
  unfold indexLengthCheck constant
  rw [if_neg (by decide)]
  cases r <;> first | exact absurd rfl h | rfl

theorem indexLengthCheck_mem (s : MachineState) :
    (indexLengthCheck.foldl execInstrBr s).mem = s.mem := by
  unfold indexLengthCheck constant
  rw [if_neg (by decide)]
  rfl

theorem checkedIndexState_pc (s : MachineState)
    (scratch : s.getReg .x19 = BitVec.ofNat 64 scratchBase) :
    (checkedIndexState s).pc = s.pc + 996 := by
  simp only [checkedIndexState, skipReject, MachineState.setPC]
  rw [Riscv.linear_fold_pc _ _ (indexLengthCheck_ready _),
    Riscv.linear_fold_pc _ _ (nibbleChecks_ready s scratch), nibbleChecks_length,
    indexLengthCheck_length]
  change (((s.pc + 952) + 16) + 12) + 16 = s.pc + 996
  simp only [BitVec.add_assoc]
  rfl

theorem checkedIndexState_code (s : MachineState) : (checkedIndexState s).code = s.code := by
  simp only [checkedIndexState, skipReject, MachineState.code_setPC, Riscv.fold_code]

theorem checkedIndexState_mem (s : MachineState) :
    (checkedIndexState s).mem = (nibbleChecks.foldl execInstrBr s).mem := by
  unfold checkedIndexState skipReject
  generalize nibbleChecks.foldl execInstrBr s = a
  change (indexLengthCheck.foldl execInstrBr (a.setPC (a.pc + 16))).mem = a.mem
  rw [indexLengthCheck_mem]
  rfl

theorem checkedIndexState_reg (s : MachineState) (r : Reg) (h : r ≠ .x26) :
    (checkedIndexState s).getReg r = (nibbleChecks.foldl execInstrBr s).getReg r := by
  unfold checkedIndexState skipReject
  generalize nibbleChecks.foldl execInstrBr s = a
  rw [MachineState.getReg_setPC, indexLengthCheck_preserves _ r h, MachineState.getReg_setPC]

theorem checkedIndexState_base (s : MachineState) :
    (checkedIndexState s).getReg .x8 = BitVec.ofNat 64 positionsBase := by
  rw [checkedIndexState_reg s .x8 (by decide)]
  exact (nibbleChecks_effect s).2.1

theorem checkedIndexState_rank (s : MachineState) : rankOf (checkedIndexState s) = indexOf s := by
  rw [rankOf, checkedIndexState_reg s .x20 (by decide), checkedIndexState_reg s .x21 (by decide)]
  exact (nibbleChecks_effect s).2.2.2.1

/-- The checked state changes memory only in the 36-word position array. -/
theorem checked_frame (s : MachineState) (addr : Word)
    (outside : addr.toNat < positionsBase ∨ positionsBase + 288 ≤ addr.toNat) :
    (checkedIndexState s).getMem addr = s.getMem addr := by
  change (checkedIndexState s).mem addr = s.mem addr
  rw [checkedIndexState_mem]
  refine (nibbleChecks_effect s).2.2.2.2.2.2.1 addr fun k hk e => ?_
  have := congrArg BitVec.toNat e
  rw [positionAddr_toNat k hk] at this
  unfold positionsBase at this outside
  omega

/-- The stored chain positions: `14 - nibble` for the first 32 chains, 14 for the last four. -/
theorem checked_position (s : MachineState) (k : ℕ) (hk : k < 36) :
    (checkedIndexState s).getMem (positionAddr k) =
      if k < 32 then (14 : Word) - BitVec.ofNat 64 (nibble (indexOf s) k) else 14 := by
  change (checkedIndexState s).mem (positionAddr k) = _
  rw [checkedIndexState_mem]
  by_cases h32 : k < 32
  · rw [if_pos h32]
    exact (nibbleChecks_effect s).2.2.2.2.1 k h32
  · rw [if_neg h32]
    exact (nibbleChecks_effect s).2.2.2.2.2.1 k (by omega) hk

/-- The checked state retains the actual oracle index in its two index registers. -/
theorem checkedIndexState_hash_rank (image : Riscv.Image) (pk : PublicKey paperParams)
    (m : Message paperParams) (bits : List Bool) (answer : BitVec 256) :
    rankOf (checkedIndexState (Riscv.writeHash (indexInputState image pk m bits) answer)) =
      (answer.setWidth 128).toNat := by
  rw [checkedIndexState_rank]
  have low := writeHash_word (indexInputState image pk m bits) answer 0 (by decide)
  have high := writeHash_word (indexInputState image pk m bits) answer 1 (by decide)
  change (Riscv.writeHash (indexInputState image pk m bits) answer).getMem
    (BitVec.ofNat 64 (scratchBase + 128)) = answer.extractLsb' 0 64 at low
  change (Riscv.writeHash (indexInputState image pk m bits) answer).getMem
    (BitVec.ofNat 64 (scratchBase + 136)) = answer.extractLsb' 64 64 at high
  change (joinWords
    ((Riscv.writeHash (indexInputState image pk m bits) answer).getMem
      (BitVec.ofNat 64 (scratchBase + 128)))
    ((Riscv.writeHash (indexInputState image pk m bits) answer).getMem
      (BitVec.ofNat 64 (scratchBase + 136)))).toNat = _
  rw [low, high, answer_low128]

/-- The accepted index as a valid index. -/
def acceptedIdx (answer : BitVec 256) (hi : Accepted (answer.setWidth 128).toNat) : Idx paperParams :=
  ⟨(answer.setWidth 128).toNat, mem_validSet.mpr ⟨(answer.setWidth 128).isLt, hi⟩⟩

theorem acceptedIdx_val (answer : BitVec 256) (hi : Accepted (answer.setWidth 128).toNat) :
    (acceptedIdx answer hi).val = (answer.setWidth 128).toNat := rfl

theorem indexOf_hash (image : Riscv.Image) (pk : PublicKey paperParams)
    (m : Message paperParams) (bits : List Bool) (answer : BitVec 256) :
    indexOf (Riscv.writeHash (indexInputState image pk m bits) answer) =
      (answer.setWidth 128).toNat := by
  rw [← checkedIndexState_hash_rank image pk m bits answer, checkedIndexState_rank]

end OptimalOTS.RiscvUpperProgram
