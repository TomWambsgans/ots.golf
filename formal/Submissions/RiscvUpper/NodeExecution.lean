import Submissions.RiscvUpper.NodeReady
import Submissions.RiscvUpper.NodeRefinement
import Submissions.RiscvUpper.NodeValueProof
import Submissions.RiscvUpper.CursorBudget
import Submissions.RiscvUpper.ExecutionContext

/-! Sequential machine reconstruction with the specification's disclosure cursor. -/

namespace OptimalOTS.RiscvUpperProgram.Direct

open RiscvZkvm.Rv64 Forest Forest.Name RiscvUpperForest.ForestVerifier OracleComp

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option allowUnsafeReducibility true
attribute [local reducible] Forest.graph
attribute [local irreducible] Forest.fixedPositions Forest.fixedDigits

theorem SlotFrame.below {s t : MachineState} {dest : Name} (frame : SlotFrame s t dest) :
    FrameBelow s t := by
  intro addr below
  apply frame
  intro j hj heq
  have h := congrArg BitVec.toNat heq
  have bounds := slotAddress_bounds dest
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at h
  change addr.toNat < 7340032 at below
  omega

theorem disclosed_length (positions : Fin 63 → Fin 15) (n : Name)
    (disclosed : RiscvUpperForest.ForestVerifier.disclosed positions n = true) : n.len = 128 := by
  cases n <;> simp_all [RiscvUpperForest.ForestVerifier.disclosed, Name.len]

theorem disclosed_not_evaluated (positions : Fin 63 → Fin 15) (n : Name)
    (hd : disclosed positions n = true) : evaluated positions n = false := by
  cases n <;> simp_all [disclosed, evaluated]

/-- The mandatory part of a node prepares its slot and its two branch flags. -/
def setupState (s : MachineState) (n : Name) : MachineState :=
  (constant .x18 (slotAddress n) ++ clearSlot ++ guards n).foldl execInstrBr s

theorem setupState_destination (s : MachineState) (n : Name) :
    (setupState s n).getReg .x18 = BitVec.ofNat 64 (slotAddress n) := by
  simp only [setupState, List.foldl_append,
    guards_register _ n .x18 (by decide) (by decide) (by decide) (by decide),
    clearSlot_registers, constant_value _ .x18 _ (by decide), slotAddress_literal]

theorem setupState_register (s : MachineState) (n : Name) (r : Reg)
    (h18 : r ≠ .x18) (h24 : r ≠ .x24) (h25 : r ≠ .x25)
    (h26 : r ≠ .x26) (h27 : r ≠ .x27) :
    (setupState s n).getReg r = s.getReg r := by
  simp only [setupState, List.foldl_append, guards_register _ _ _ h24 h25 h26 h27,
    clearSlot_registers, constant_preserves _ .x18 r _ h18.symm]

theorem setupState_frame (s : MachineState) (n : Name) : SlotFrame s (setupState s n) n := by
  intro addr outside
  have cleared := congrFun (clearSlot_memory ((constant .x18 (slotAddress n)).foldl execInstrBr s)) addr
  change (clearSlot.foldl execInstrBr _).getMem addr = _ at cleared
  change (setupState s n).mem addr = s.mem addr
  simp only [setupState, List.foldl_append, guards_memory]
  change (clearSlot.foldl execInstrBr _).getMem addr = s.getMem addr
  rw [cleared]
  change (MachineState.writeWords _ _ _).getMem addr = s.getMem addr
  rw [getMem_writeWords_of_disjoint]
  · exact congrFun (constant_mem s .x18 (slotAddress n)) addr
  · intro j hj
    rw [constant_value _ .x18 _ (by decide), slotAddress_literal]
    exact outside j (by simpa using hj)

theorem setupState_context {s : MachineState} {index : Fin (2 ^ 115)}
    {payload : List Bool} {pk : PublicKey paperParams}
    (context : ExecutionContext s index payload pk) (n : Name) :
    ExecutionContext (setupState s n) index payload pk :=
  context.frame (setupState_frame s n).below
    (setupState_register s n .x8 (by decide) (by decide) (by decide) (by decide) (by decide))

theorem setupState_other (s : MachineState) (n : Name) (x : graph.Assignment)
    (stored : NodeStorage s x) : OtherStorage (setupState s n) x n := by
  intro other different
  exact (setupState_frame s n).other different.symm _
    (by rw [graph_len_fin]; exact (node_length_bound other).trans (by decide)) (stored other)

theorem setupState_zero (s : MachineState) (n : Name) :
    MemBits (setupState s n) (BitVec.ofNat 64 (slotAddress n)) (0 : BitVec n.len) := by
  apply memBits_of_mem_eq (show (setupState s n).mem =
    (clearSlot.foldl execInstrBr ((constant .x18 (slotAddress n)).foldl execInstrBr s)).mem by
      simp only [setupState, List.foldl_append, guards_memory])
  exact clearSlot_zero _ n (by rw [constant_value _ .x18 _ (by decide), slotAddress_literal])

theorem setupState_guards {s : MachineState} {index : Fin (2 ^ 115)}
    {payload : List Bool} {pk : PublicKey paperParams}
    (context : ExecutionContext s index payload pk) (n : Name) :
    (setupState s n).getReg .x24 = BitVec.ofNat 64 (disclosed (fixedPositions index) n).toNat ∧
    (setupState s n).getReg .x25 = BitVec.ofNat 64 (evaluated (fixedPositions index) n).toNat := by
  have positions : PositionMemory
      (clearSlot.foldl execInstrBr ((constant .x18 (slotAddress n)).foldl execInstrBr s))
      (fixedPositions index) := by
    intro k hk
    have h := (setupState_context context n).positions k hk
    simpa only [setupState, List.foldl_append,
      guards_register _ n .x8 (by decide) (by decide) (by decide) (by decide),
      MachineState.getMem, guards_memory] using h
  have h := guards_values _ (fixedPositions index) n positions
  simpa only [setupState, List.foldl_append] using h

theorem readDisclosure_register (s : MachineState) (r : Reg)
    (h9 : r ≠ .x9) (h26 : r ≠ .x26) (h27 : r ≠ .x27) :
    (readDisclosure.foldl execInstrBr s).getReg r = s.getReg r := by
  simp only [readDisclosure, List.foldl_append, List.foldl_cons, List.foldl_nil, execInstrBr,
    MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ .x9 r _ h9.symm,
    copy128_reg _ .x9 .x18 r 0 0 h26 h27]

theorem readDisclosure_cursor (s : MachineState) :
    (readDisclosure.foldl execInstrBr s).getReg .x9 = s.getReg .x9 + 16 := rfl

theorem readDisclosure_frame (s : MachineState) (n : Name)
    (destination : s.getReg .x18 = BitVec.ofNat 64 (slotAddress n)) :
    SlotFrame s (readDisclosure.foldl execInstrBr s) n := by
  intro addr outside
  have same : (readDisclosure.foldl execInstrBr s).getMem addr =
      ((copy128 .x9 0 .x18 0).foldl execInstrBr s).getMem addr := rfl
  rw [same, copy128_getMem _ _ _ _ _ (by decide) (by decide) (by decide)]
  rw [show signExtend12 (BitVec.ofNat 12 (0 + 8)) = (8 : Word) by rfl,
    show signExtend12 (BitVec.ofNat 12 0) = (0 : Word) by rfl, destination]
  have h1 : addr ≠ BitVec.ofNat 64 (slotAddress n) + 8 := outside 1 (by decide)
  have h0 : addr ≠ BitVec.ofNat 64 (slotAddress n) + 0 := outside 0 (by decide)
  rw [if_neg h1, if_neg h0]

theorem readDisclosure_value (s : MachineState) (n : Name) (value : BitVec 128)
    (destination : s.getReg .x18 = BitVec.ofNat 64 (slotAddress n))
    (aligned : alignToDword (s.getReg .x9) = s.getReg .x9)
    (source : MemBits s (s.getReg .x9) value) :
    MemBits (readDisclosure.foldl execInstrBr s) (BitVec.ofNat 64 (slotAddress n)) value := by
  have h := copy128_memBits s .x9 .x18 0 0 (by decide) (by decide) (by decide)
    (by decide) (by decide)
    (by simpa only [BitVec.add_zero] using aligned)
    (by simpa only [destination, BitVec.add_zero] using slot_aligned n) value
    (by simpa only [BitVec.add_zero] using source)
  apply memBits_of_mem_eq (show (readDisclosure.foldl execInstrBr s).mem =
    ((copy128 .x9 0 .x18 0).foldl execInstrBr s).mem from rfl)
  simpa only [destination, BitVec.add_zero] using h

theorem OtherStorage.update {s : MachineState} {x : graph.Assignment} {n : Name}
    (others : OtherStorage s x n) (value : BitVec (graph.len n.fin))
    (represented : MemBits s (BitVec.ofNat 64 (slotAddress n)) value) :
    NodeStorage s (Function.update x n.fin value) :=
  nodeStorage_update s x n value others represented

theorem SlotFrame.setPC {s t : MachineState} {dest : Name} (frame : SlotFrame s t dest)
    (pc : Word) : SlotFrame s (t.setPC pc) dest := by
  intro addr h
  rw [MachineState.getMem_setPC]
  exact frame addr h

theorem memBits_setPC {n : ℕ} {s : MachineState} {base : Word} {v : BitVec n} (pc : Word) :
    MemBits (s.setPC pc) base v ↔ MemBits s base v := by
  simp only [MemBits, MachineState.getByte, MachineState.getMem_setPC]

theorem OtherStorage.setPC {s : MachineState} {x : graph.Assignment} {dest : Name}
    (stored : OtherStorage s x dest) (pc : Word) : OtherStorage (s.setPC pc) x dest :=
  fun n different => (memBits_setPC pc).mpr (stored n different)

theorem NodeStorage.setPC {s : MachineState} {x : graph.Assignment}
    (stored : NodeStorage s x) (pc : Word) : NodeStorage (s.setPC pc) x :=
  fun n => (memBits_setPC pc).mpr (stored n)

theorem readDisclosure_length : readDisclosure.length = 5 := rfl

/-- The disclosure branch follows the flag computed from the decoded positions. -/
theorem nodePrelude_effect {s : MachineState} {index : Fin (2 ^ 115)}
    {payload : List Bool} {pk : PublicKey paperParams}
    (context : ExecutionContext s index payload pk) (n : Name) :
    (nodePrelude n).eval s =
      if disclosed (fixedPositions index) n then
        readDisclosure.foldl execInstrBr ((setupState s n).setPC ((setupState s n).pc + 4))
      else (setupState s n).setPC ((setupState s n).pc + 24) := by
  have guards := (setupState_guards context n).1
  have passed : PureBlock.passes false .x24 (setupState s n) ↔
      disclosed (fixedPositions index) n = true := by
    unfold PureBlock.passes
    rw [guards]
    cases disclosed (fixedPositions index) n <;> decide
  have unfolded : (nodePrelude n).eval s =
      if PureBlock.passes false .x24 (setupState s n) then
        readDisclosure.foldl execInstrBr
          (PureBlock.branchState false .x24 readDisclosure.length (setupState s n))
      else PureBlock.branchState false .x24 readDisclosure.length (setupState s n) := by
    simp only [nodePrelude, PureBlock.eval, PureBlock.code, setupState]
    try rfl
  rw [unfolded]
  by_cases hd : disclosed (fixedPositions index) n = true
  · have hp := passed.mpr hd
    rw [if_pos hp, if_pos hd]
    simp only [PureBlock.branchState, if_pos hp]
  · have hp := mt passed.mp hd
    rw [if_neg hp, if_neg hd]
    simp only [PureBlock.branchState, if_neg hp, readDisclosure_length]
    rfl

theorem nodePrelude_frame {s : MachineState} {index : Fin (2 ^ 115)}
    {payload : List Bool} {pk : PublicKey paperParams}
    (context : ExecutionContext s index payload pk) (n : Name) :
    SlotFrame s ((nodePrelude n).eval s) n := by
  rw [nodePrelude_effect context]
  split
  · exact ((setupState_frame s n).setPC _).trans
      (readDisclosure_frame _ n (by rw [MachineState.getReg_setPC]; exact setupState_destination s n))
  · exact (setupState_frame s n).setPC _

theorem nodePrelude_register {s : MachineState} {index : Fin (2 ^ 115)}
    {payload : List Bool} {pk : PublicKey paperParams}
    (context : ExecutionContext s index payload pk) (n : Name) (r : Reg)
    (h9 : r ≠ .x9) (h18 : r ≠ .x18) (h24 : r ≠ .x24) (h25 : r ≠ .x25)
    (h26 : r ≠ .x26) (h27 : r ≠ .x27) :
    ((nodePrelude n).eval s).getReg r = s.getReg r := by
  rw [nodePrelude_effect context]
  split
  · rw [readDisclosure_register _ _ h9 h26 h27, MachineState.getReg_setPC]
    exact setupState_register s n r h18 h24 h25 h26 h27
  · rw [MachineState.getReg_setPC]
    exact setupState_register s n r h18 h24 h25 h26 h27

theorem nodePrelude_context {s : MachineState} {index : Fin (2 ^ 115)}
    {payload : List Bool} {pk : PublicKey paperParams}
    (context : ExecutionContext s index payload pk) (n : Name) :
    ExecutionContext ((nodePrelude n).eval s) index payload pk :=
  context.frame (nodePrelude_frame context n).below
    (nodePrelude_register context n .x8 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide))

theorem nodePrelude_cursor {s : MachineState} {index : Fin (2 ^ 115)}
    {payload : List Bool} {pk : PublicKey paperParams}
    (context : ExecutionContext s index payload pk) (n : Name) (cursor : ℕ)
    (atCursor : CursorAt s cursor) (aligned : cursor % 128 = 0) :
    CursorAt ((nodePrelude n).eval s) (cursor + consumedBits index n) := by
  unfold CursorAt
  rw [nodePrelude_effect context, consumedBits_word]
  split
  · rw [readDisclosure_cursor, MachineState.getReg_setPC,
      setupState_register _ _ .x9 (by decide) (by decide) (by decide) (by decide) (by decide), atCursor]
    rw [show (cursor + 128) / 8 = cursor / 8 + 16 by omega, BitVec.ofNat_add,
      ← BitVec.add_assoc]
    rfl
  · rw [Nat.add_zero, MachineState.getReg_setPC,
      setupState_register _ _ .x9 (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact atCursor

theorem nodePrelude_flag {s : MachineState} {index : Fin (2 ^ 115)}
    {payload : List Bool} {pk : PublicKey paperParams}
    (context : ExecutionContext s index payload pk) (n : Name) :
    ((nodePrelude n).eval s).getReg .x25 =
      BitVec.ofNat 64 (evaluated (fixedPositions index) n).toNat := by
  rw [nodePrelude_effect context]
  split
  · rw [readDisclosure_register _ .x25 (by decide) (by decide) (by decide), MachineState.getReg_setPC]
    exact (setupState_guards context n).2
  · rw [MachineState.getReg_setPC]
    exact (setupState_guards context n).2

/-- Clearing and optional disclosure reading initialize the destination's graph value. -/
theorem nodePrelude_value {s : MachineState} {index : Fin (2 ^ 115)}
    {payload : List Bool} {pk : PublicKey paperParams}
    (context : ExecutionContext s index payload pk) (n : Name) (cursor : ℕ)
    (atCursor : CursorAt s cursor) (aligned : cursor % 128 = 0)
    (bounded : cursor + consumedBits index n ≤ 5248) :
    MemBits ((nodePrelude n).eval s) (BitVec.ofNat 64 (slotAddress n))
      (if disclosed (fixedPositions index) n then
        ofBits (graph.len n.fin) ((payload.drop cursor).take (graph.len n.fin)) else 0) := by
  rw [nodePrelude_effect context]
  split_ifs with hd
  · have length : graph.len n.fin = 128 := (graph_len_fin n).trans (disclosed_length _ n hd)
    have needed : cursor + 128 ≤ 5248 := by
      simpa only [consumedBits_word, hd, if_true] using bounded
    let start := (setupState s n).setPC ((setupState s n).pc + 4)
    have startContext : ExecutionContext start index payload pk :=
      (setupState_context context n).setPC _
    have startCursor : CursorAt start cursor := by
      unfold CursorAt
      rw [MachineState.getReg_setPC,
        setupState_register _ _ .x9 (by decide) (by decide) (by decide) (by decide) (by decide)]
      exact atCursor
    rw [length]
    have take : ofBits 128 ((payload.drop cursor).take 128) = ofBits 128 (payload.drop cursor) := by
      simpa only [List.drop_zero] using
        ofBits_drop_take (payload.drop cursor) (cap := 128) (start := 0) (len := 128) (by decide)
    rw [take]
    apply readDisclosure_value start n _
      (by rw [MachineState.getReg_setPC]; exact setupState_destination s n)
    · apply (aligned_iff _).mpr
      exact (startCursor.ready (by omega) aligned).2.2
    · exact startContext.payload_word cursor startCursor aligned needed
  · apply (memBits_setPC _).mpr
    have zero := setupState_zero s n
    intro j hj
    have h := zero j (by rwa [← graph_len_fin])
    exact h

/-- All other node values survive the mandatory clear and optional disclosure read. -/
theorem nodePrelude_other {s : MachineState} {index : Fin (2 ^ 115)}
    {payload : List Bool} {pk : PublicKey paperParams}
    (context : ExecutionContext s index payload pk) (n : Name) (x : graph.Assignment)
    (stored : NodeStorage s x) : OtherStorage ((nodePrelude n).eval s) x n := by
  intro other different
  exact (nodePrelude_frame context n).other different.symm _
    (by rw [graph_len_fin]; exact (node_length_bound other).trans (by decide)) (stored other)

/-- Reify the machine state corresponding to one specified cursor step. -/
def transitionState (s : MachineState) (index : Fin (2 ^ 115)) (n : Name)
    (result : graph.Assignment × ℕ) : MachineState :=
  let prepared := (nodePrelude n).eval s
  if evaluated (fixedPositions index) n then
    nodeResult (prepared.setPC (prepared.pc + 4)) n (result.1 n.fin)
  else prepared.setPC (prepared.pc + BitVec.ofNat 64 (4 * ((operation (nodeOp n)).length + 1)))

/-- The node compiler preserves the complete oracle computation and its cursor update. -/
theorem nodeEffect_eq {s : MachineState} {index : Fin (2 ^ 115)}
    {payload : List Bool} {pk : PublicKey paperParams}
    (context : ExecutionContext s index payload pk) (n : Name) (x : graph.Assignment)
    (stored : NodeStorage s x) (cursor : ℕ) :
    nodeEffect s n = transitionState s index n <$> cursorStep index payload x cursor n := by
  have other := nodePrelude_other context n x stored
  have flag := nodePrelude_flag context n
  by_cases hd : disclosed (fixedPositions index) n = true
  · have he := disclosed_not_evaluated (fixedPositions index) n hd
    have zero : ((nodePrelude n).eval s).getReg .x25 = 0 := by rw [flag, he]; rfl
    simp only [nodeEffect, guardEffect, zero, cursorStep, hd, map_pure, transitionState, he,
      Bool.false_eq_true, if_false, if_true]
  · cases he : evaluated (fixedPositions index) n with
    | false =>
      have zero : ((nodePrelude n).eval s).getReg .x25 = 0 := by rw [flag, he]; rfl
      simp only [nodeEffect, guardEffect, zero, cursorStep, hd, he, map_pure, transitionState,
        Bool.false_eq_true, if_false, if_true]
    | true =>
      have nonzero : ((nodePrelude n).eval s).getReg .x25 ≠ 0 := by rw [flag, he]; decide
      simp only [nodeEffect, guardEffect, nonzero, cursorStep, hd, he, Bool.false_eq_true,
        if_false, if_true, runOp_eq]
      rw [operationEffect_eq _ n x (other.setPC _), Functor.map_map]
      apply congrArg (fun f => f <$> evalName x n)
      funext value
      simp only [transitionState, he, if_true, Function.update_self]

end OptimalOTS.RiscvUpperProgram.Direct
