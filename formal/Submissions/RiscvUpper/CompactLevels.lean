import Submissions.RiscvUpper.CompactChains

/-!
# The chain phase

The 36 active chains run as consecutive blocks in the specification's chain-major node order;
inactive chains have no code. The setup fixes the base registers and the payload pointer; the
epilogue advances the disclosure cursor past the 36 chain words for the tree phase.
-/

namespace OptimalOTS.RiscvUpperProgram.Compact

open RiscvZkvm.Rv64 Forest Forest.Name RiscvUpperForest.ForestVerifier OracleComp

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option allowUnsafeReducibility true
attribute [local reducible] Forest.graph
attribute [local irreducible] Forest.fixedPositions Forest.fixedDigits

/-- The tree nodes following every chain node. -/
def treeNodes : List Name :=
  (List.finRange 21).map gc ++ (List.finRange 21).map gh ++ (List.finRange 21).map gv ++
  (List.finRange 7).map ec ++ (List.finRange 7).map eh ++ (List.finRange 7).map ev ++ [rc, rh]

/-- Chains `k` and later, in specification order. -/
def chainsFrom (k : ℕ) : List Name :=
  if h : k < 63 then chainNodes ⟨k, h⟩ ++ chainsFrom (k + 1) else []
termination_by 63 - k

/-- The blocks of active chains `k` and later. -/
def blocksFrom (k : ℕ) : Code :=
  if k < 36 then chainBlock k ++ blocksFrom (k + 1) else []
termination_by 36 - k

theorem chainsFrom_zero : (List.finRange 63).flatMap chainNodes = chainsFrom 0 := by
  decide +kernel

theorem order_split : order = chainsFrom 0 ++ treeNodes := by
  rw [← chainsFrom_zero]
  simp only [order, treeNodes, List.append_assoc]

theorem blocks_eq : (List.range 36).flatMap chainBlock = blocksFrom 0 := by
  decide +kernel

theorem blocksFrom_nil (k : ℕ) (hk : ¬ k < 36) : blocksFrom k = [] := by
  rw [blocksFrom, if_neg hk]

theorem blocksFrom_cons (k : ℕ) (hk : k < 36) : blocksFrom k = chainBlock k ++ blocksFrom (k + 1) := by
  rw [blocksFrom, if_pos hk]

/-- A segment charging exactly its code length costs the code's length in total. -/
theorem cost_eq_length (seg : Segment) (nodes : List Name)
    (h : ∀ n ∈ nodes, seg.cost n = (seg.code n).length) :
    (nodes.map seg.cost).sum = (nodes.flatMap seg.code).length := by
  rw [List.length_flatMap]
  congr 1
  exact List.map_congr_left h

variable (index : Idx paperParams) (payload : List Bool) (pk : PublicKey paperParams)

/-- The cycles of chains `k` and later: `13 + 3 (14 - p)` for each active chain. -/
def costFrom (k : ℕ) : ℕ :=
  if h : k < 63 then
    (if k < 36 then 13 + 3 * (14 - pos index ⟨k, h⟩) else 0) + costFrom (k + 1)
  else 0
termination_by 63 - k

theorem costFrom_eq : ∀ (n k : ℕ), 63 - k = n → costFrom index k =
    ∑ k' : Fin 63, if k ≤ k'.val ∧ k'.val < 36 then 13 + 3 * (14 - pos index k') else 0 := by
  intro n
  induction n with
  | zero =>
    intro k hk
    rw [costFrom, dif_neg (by omega)]
    symm
    apply Finset.sum_eq_zero
    intro k' _
    rw [if_neg]
    have := k'.isLt
    omega
  | succ n ih =>
    intro k hk
    have hk63 : k < 63 := by omega
    rw [costFrom, dif_pos hk63, ih (k + 1) (by omega)]
    have single : (if k < 36 then 13 + 3 * (14 - pos index ⟨k, hk63⟩) else 0) =
        ∑ k' : Fin 63, if k' = ⟨k, hk63⟩ then
          (if k ≤ k'.val ∧ k'.val < 36 then 13 + 3 * (14 - pos index k') else 0) else 0 := by
      rw [Finset.sum_ite_eq' Finset.univ (⟨k, hk63⟩ : Fin 63)
        (fun k' : Fin 63 => if k ≤ k'.val ∧ k'.val < 36 then 13 + 3 * (14 - pos index k') else 0),
        if_pos (Finset.mem_univ _)]
      simp only [Fin.val_mk, le_refl, true_and]
    rw [single, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k' _
    by_cases he : k' = ⟨k, hk63⟩
    · subst he
      simp only [↓reduceIte, Fin.val_mk, le_refl, true_and]
      split_ifs <;> omega
    · rw [if_neg he, Nat.zero_add]
      have hne : k'.val ≠ k := fun h => he (Fin.ext h)
      split_ifs <;> omega

/-- Tree-node disclosure does not depend on the index. -/
def treeBits (n : Name) : ℕ := if disclosed (fun _ => 0) n then n.len else 0

/-- The tree phase reads exactly five words: three group values and two subtree values. -/
theorem tree_consumed : (treeNodes.map (consumedBits index)).sum = 640 := by
  have pointwise : ∀ n ∈ treeNodes, consumedBits index n = treeBits n := by
    intro n hn
    simp only [treeNodes, List.mem_append, List.mem_map, List.mem_finRange, true_and,
      List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, or_assoc] at hn
    rcases hn with ⟨j, rfl⟩ | ⟨j, rfl⟩ | ⟨j, rfl⟩ | ⟨l, rfl⟩ | ⟨l, rfl⟩ | ⟨l, rfl⟩ | rfl | rfl <;> rfl
  rw [List.map_congr_left pointwise]
  decide +kernel

/-! ## The whole chain phase -/

theorem chainSetup_effect (s : MachineState) :
    (chainSetup.foldl execInstrBr s).getReg .x18 = BitVec.ofNat 64 chainsBase ∧
    (chainSetup.foldl execInstrBr s).getReg .x9 = Riscv.signatureBase + 32 ∧
    (chainSetup.foldl execInstrBr s).getReg .x5 = Riscv.hashCall ∧
    (chainSetup.foldl execInstrBr s).getReg .x11 = 144 ∧
    (∀ r, r ≠ .x18 → r ≠ .x9 → r ≠ .x5 → r ≠ .x11 →
      (chainSetup.foldl execInstrBr s).getReg r = s.getReg r) ∧
    (chainSetup.foldl execInstrBr s).mem = s.mem := by
  have baseLit : literalValue chainsBase = BitVec.ofNat 64 chainsBase := by decide +kernel
  have cursorLit : literalValue (Riscv.signatureBase.toNat + 32) = Riscv.signatureBase + 32 := by
    decide +kernel
  simp only [chainSetup, List.foldl_append, List.foldl_cons, List.foldl_nil, execInstrBr]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ .x11 .x18 _ (by decide),
      MachineState.getReg_setReg_ne _ .x5 .x18 _ (by decide),
      constant_preserves _ .x9 .x18 _ (by decide), constant_value _ .x18 _ (by decide), baseLit]
  · simp only [MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ .x11 .x9 _ (by decide),
      MachineState.getReg_setReg_ne _ .x5 .x9 _ (by decide),
      constant_value _ .x9 _ (by decide), cursorLit]
  · simp only [MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ .x11 .x5 _ (by decide),
      MachineState.getReg_setReg_eq (by decide : Reg.x5 ≠ .x0), getReg_x0]
    try rfl
  · simp only [MachineState.getReg_setPC, MachineState.getReg_setReg_eq (by decide : Reg.x11 ≠ .x0),
      getReg_x0]
    try rfl
  · intro r h18 h9 h5 h11
    simp only [MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ .x11 r _ h11.symm,
      MachineState.getReg_setReg_ne _ .x5 r _ h5.symm, constant_preserves _ .x9 r _ h9.symm,
      constant_preserves _ .x18 r _ h18.symm]
  · simp only [MachineState.setPC, MachineState.setReg, constant_mem]
    try rfl

theorem chainSetup_ready (s : MachineState) : Riscv.LinearReady s chainSetup := by
  refine ((constant_ready _ _ _).append (constant_ready _ _ _)).append ?_
  exact ⟨rfl, trivial, rfl, trivial, trivial⟩

theorem chainSetup_length : chainSetup.length = 6 := by decide +kernel

theorem chainsEnd_effect (s : MachineState) :
    (chainsEnd.foldl execInstrBr s).getReg .x9 = s.getReg .x9 + BitVec.ofNat 64 576 ∧
    (∀ r, r ≠ .x9 → (chainsEnd.foldl execInstrBr s).getReg r = s.getReg r) ∧
    (chainsEnd.foldl execInstrBr s).mem = s.mem := by
  have h576 : signExtend12 576 = BitVec.ofNat 64 576 := by decide
  simp only [chainsEnd, List.foldl_cons, List.foldl_nil, execInstrBr, h576]
  refine ⟨?_, ?_, rfl⟩
  · simp only [MachineState.getReg_setPC, MachineState.getReg_setReg_eq (by decide : Reg.x9 ≠ .x0)]
  · intro r h9
    simp only [MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ .x9 r _ h9.symm]

theorem chainsEnd_ready (s : MachineState) : Riscv.LinearReady s chainsEnd := ⟨rfl, trivial, trivial⟩

theorem chainsEnd_length : chainsEnd.length = 1 := rfl

/-- After the last chain every active chain holds its final value and the cursor names the first
tree word. -/
def ChainsDone (s : MachineState) (x : graph.Assignment) (cursor : ℕ) : Prop :=
  ChainCtx index payload pk s cursor treeNodes ∧
  ∀ k : Fin 63, k.val < 36 → Holds s k (x (cv k 13).fin)

/-- Chains `k` and later refine the reader over their nodes. -/
theorem chainsFrom_refines (tail : Code)
    (K : graph.Assignment × ℕ → OracleComp (Spec paperParams) (Option Bool)) (c rest' : ℕ)
    (continuation : ∀ (u : MachineState) (y : graph.Assignment),
      ChainsInv index payload pk u y 63 → Riscv.CodeAt u u.pc tail →
      ∀ left, rest' ≤ left → Riscv.Refines left u (K (y, 4608)) c) :
    ∀ (n k : ℕ), 63 - k = n →
    ∀ (s : MachineState) (x : graph.Assignment) (fuel cursor : ℕ), cursor = 128 * min k 36 →
      ChainsInv index payload pk s x k →
      Riscv.CodeAt s s.pc (blocksFrom k ++ tail) →
      (blocksFrom k).length + rest' ≤ fuel →
      Riscv.Refines fuel s (runNodes' index payload (chainsFrom k) x cursor >>= K)
        (costFrom index k + c) := by
  intro n
  induction n with
  | zero =>
    intro k hk s x fuel cursor hcursor inv located bound
    have hk63 : ¬ k < 63 := by omega
    rw [chainsFrom, dif_neg hk63, costFrom, dif_neg hk63, Nat.zero_add, runNodes', pure_bind,
      hcursor, show min k 36 = 36 by omega]
    rw [blocksFrom_nil k (by omega), List.nil_append] at located
    rw [blocksFrom_nil k (by omega), List.length_nil, Nat.zero_add] at bound
    exact continuation s x ⟨inv.context, inv.regs, inv.cursorReg, inv.pcAligned,
      fun k' hk' _ => inv.done k' hk' (by omega)⟩ located fuel bound
  | succ n ih =>
    intro k hk s x fuel cursor hcursor inv located bound
    have hk63 : k < 63 := by omega
    rw [chainsFrom, dif_pos hk63, costFrom, dif_pos hk63, runNodes'_append, bind_assoc]
    by_cases h36 : k < 36
    · rw [if_pos h36, hcursor, show min k 36 = k by omega]
      rw [blocksFrom_cons k h36, List.append_assoc] at located
      rw [blocksFrom_cons k h36, List.length_append, chainBlock_length k h36] at bound
      have hpos : pos index ⟨k, hk63⟩ ≤ 14 := by
        show (fixedPositions index ⟨k, hk63⟩).val ≤ 14
        have := (fixedPositions index ⟨k, hk63⟩).isLt
        omega
      rw [Nat.add_assoc]
      apply chain_refines index payload pk ⟨k, hk63⟩ h36 (blocksFrom (k + 1) ++ tail)
        (fun r => runNodes' index payload (chainsFrom (k + 1)) r.1 r.2 >>= K)
        (costFrom index (k + 1) + c) ((blocksFrom (k + 1)).length + rest') ?_ s x fuel inv located
        (by omega)
      intro u y inv' located' left hleft
      dsimp only
      exact ih (k + 1) (by omega) u y left (128 * k + 128) (by omega) inv' located' hleft
    · rw [if_neg h36, Nat.zero_add]
      have hb0 : blocksFrom k = [] := blocksFrom_nil k h36
      have hb1 : blocksFrom (k + 1) = [] := blocksFrom_nil (k + 1) (by omega)
      rw [hb0] at located bound
      apply inactive_refines index payload ⟨k, hk63⟩ h36 _ x cursor s fuel _
      intro y frame
      dsimp only
      apply ih (k + 1) (by omega) s y fuel cursor (by omega) ?_ ?_ ?_
      · refine ⟨inv.context, inv.regs, inv.cursorReg, inv.pcAligned, ?_⟩
        intro k' hk' _
        rw [frame k' hk']
        exact inv.done k' hk' (by omega)
      · rw [hb1]; exact located
      · rw [hb1]; exact bound

/-- The cycles of the whole chain phase for a given index. -/
def chainsCost : ℕ := chainSetup.length + costFrom index 0 + chainsEnd.length

/-- The whole chain phase refines the reader over the chain nodes of `order`. -/
theorem chains_refines (tail : Code)
    (K : graph.Assignment × ℕ → OracleComp (Spec paperParams) (Option Bool)) (c rest' : ℕ)
    (continuation : ∀ (u : MachineState) (y : graph.Assignment) (cursor' : ℕ),
      ChainsDone index payload pk u y cursor' → Riscv.CodeAt u u.pc tail →
      ∀ left, rest' ≤ left → Riscv.Refines left u (K (y, cursor')) c)
    (s : MachineState) (context : Direct.ExecutionContext s index payload pk)
    (aligned : s.pc.toNat % 4 = 0) (x : graph.Assignment) (fuel : ℕ)
    (located : Riscv.CodeAt s s.pc (chains ++ tail)) (bound : chains.length + rest' ≤ fuel) :
    Riscv.Refines fuel s (runNodes' index payload (chainsFrom 0) x 0 >>= K)
      (chainsCost index + c) := by
  have parts : chains = chainSetup ++ (blocksFrom 0 ++ chainsEnd) := by
    rw [chains, blocks_eq, List.append_assoc]
  rw [parts] at located bound
  simp only [List.append_assoc, List.length_append] at located bound
  -- the setup
  obtain ⟨h18, h9, h5, h11, regs, mem⟩ := chainSetup_effect s
  have ready := chainSetup_ready s
  have uPc := Riscv.linear_fold_pc s chainSetup ready
  have uCodeEq := Riscv.fold_code s chainSetup
  set u := chainSetup.foldl execInstrBr s with hu
  have uCode : Riscv.CodeAt u u.pc (blocksFrom 0 ++ (chainsEnd ++ tail)) := by
    rw [uPc]
    exact located.append_right.code_eq uCodeEq
  have uInv : ChainsInv index payload pk u x 0 := by
    refine ⟨context.frameInputs (fun addr _ => by simp only [MachineState.getMem, mem])
      (regs .x8 (by decide) (by decide) (by decide) (by decide)), ⟨h18, h5, h11⟩, h9, ?_, ?_⟩
    · rw [uPc, chainSetup_length, BitVec.toNat_add, BitVec.toNat_ofNat,
        Nat.mod_mod_of_dvd _ (by norm_num : 4 ∣ 2 ^ 64)]
      omega
    · intro k' _ h
      exact absurd h (Nat.not_lt_zero _)
  rw [show fuel = chainSetup.length + (fuel - chainSetup.length) by
      rw [chainSetup_length] at bound ⊢; omega,
    show chainsCost index + c = chainSetup.length + (costFrom index 0 + (chainsEnd.length + c)) by
      unfold chainsCost; omega]
  apply Riscv.Refines.linear _ located.append_left ready
  rw [← hu]
  apply chainsFrom_refines index payload pk (chainsEnd ++ tail) K (chainsEnd.length + c)
    (chainsEnd.length + rest') ?_ 63 0 rfl u x (fuel - chainSetup.length) 0 (by decide) uInv uCode
    (by rw [chainSetup_length] at bound ⊢; omega)
  intro v y invV locatedV left hleft
  -- the epilogue
  obtain ⟨v9, vRegs, vMem⟩ := chainsEnd_effect v
  have readyE := chainsEnd_ready v
  have wPc := Riscv.linear_fold_pc v chainsEnd readyE
  have wCodeEq := Riscv.fold_code v chainsEnd
  set w := chainsEnd.foldl execInstrBr v with hw
  rw [show left = chainsEnd.length + (left - chainsEnd.length) by
    rw [chainsEnd_length] at hleft ⊢; omega]
  apply Riscv.Refines.linear _ locatedV.append_left readyE
  rw [← hw]
  apply continuation w y 4608 ?_ ?_ (left - chainsEnd.length) (by omega)
  · refine ⟨⟨invV.context.frameInputs (fun addr _ => by simp only [MachineState.getMem, vMem])
      (vRegs .x8 (by decide)), ⟨?_, ?_, ?_⟩, ?_, by decide, ?_⟩, ?_⟩
    · rw [vRegs .x18 (by decide)]; exact invV.regs.base
    · rw [vRegs .x5 (by decide)]; exact invV.regs.call
    · rw [vRegs .x11 (by decide)]; exact invV.regs.length
    · show w.getReg .x9 = Riscv.signatureBase + 32 + BitVec.ofNat 64 (4608 / 8)
      rw [v9, invV.cursorReg]
    · rw [tree_consumed]
    · intro k hk
      exact memBits_of_mem_eq vMem (invV.done k hk (by omega))
  · rw [wPc]
    exact locatedV.append_right.code_eq wCodeEq

end OptimalOTS.RiscvUpperProgram.Compact
