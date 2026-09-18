import Submissions.RiscvUpper.NodeExecution

/-! Executing the node sequence refines the specification's sequential reader. -/

namespace OptimalOTS.RiscvUpperProgram.Direct

open RiscvZkvm.Rv64 Forest Forest.Name RiscvUpperForest.ForestVerifier OracleComp

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option allowUnsafeReducibility true
attribute [local reducible] Forest.graph
attribute [local irreducible] Forest.fixedPositions Forest.fixedDigits

theorem nodeCode_length (n : Name) :
    (nodeCode n).length = (nodePrelude n).code.length + ((operation (nodeOp n)).length + 1) := by
  rw [nodeCode_parts]
  simp only [List.length_append, whenNonzero, List.length_cons]

theorem pc_add_add (p : Word) (a b : ℕ) :
    p + BitVec.ofNat 64 a + BitVec.ofNat 64 b = p + BitVec.ofNat 64 (a + b) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add]

/-- Every node leaves the program counter after its code and keeps the instruction image. -/
theorem nodeEffect_pc_code (s next : MachineState) (n : Name) (ready : NodeReady s n)
    (reached : next ∈ support (nodeEffect s n)) :
    next.pc = s.pc + BitVec.ofNat 64 (4 * (nodeCode n).length) ∧ next.code = s.code := by
  have prelude_pc := PureBlock.eval_pc (nodePrelude n) s ready.1
  have prelude_code := PureBlock.eval_code (nodePrelude n) s
  rw [nodeCode_length, Nat.mul_add, ← pc_add_add, ← prelude_pc]
  unfold nodeEffect guardEffect at reached
  split_ifs at reached with zero
  · rw [mem_support_pure_iff] at reached
    subst reached
    exact ⟨rfl, prelude_code⟩
  · obtain ⟨pc, code⟩ := operationEffect_pc_code _ next (nodeOp n) (ready.2 zero) reached
    refine ⟨?_, code.trans prelude_code⟩
    rw [pc]
    change ((nodePrelude n).eval s).pc + BitVec.ofNat 64 4 +
      BitVec.ofNat 64 (4 * (operation (nodeOp n)).length) = _
    rw [pc_add_add, Nat.mul_add, Nat.mul_one, Nat.add_comm]

/-- The reconstruction invariant between consecutive nodes. -/
structure NodeState (s : MachineState) (index : Fin (2 ^ 115)) (payload : List Bool)
    (pk : PublicKey paperParams) (x : graph.Assignment) (cursor : ℕ) : Prop where
  context : ExecutionContext s index payload pk
  stored : NodeStorage s x
  atCursor : CursorAt s cursor
  aligned : cursor % 128 = 0

theorem cursorStep_snd (index : Fin (2 ^ 115)) (payload : List Bool) (x : graph.Assignment)
    (cursor : ℕ) (n : Name) (result : graph.Assignment × ℕ)
    (supported : result ∈ support (cursorStep index payload x cursor n)) :
    result.2 = cursor + consumedBits index n := by
  unfold cursorStep at supported
  split_ifs at supported with hd he
  · rw [mem_support_pure_iff] at supported
    subst supported
    rw [consumedBits_word, if_pos hd]
    exact congrArg (cursor + ·) (disclosed_length _ n hd)
  · obtain ⟨y, _, rfl⟩ := mem_support_map_peel _ _ supported
    rw [consumedBits_word, if_neg hd]
    rfl
  · rw [mem_support_pure_iff] at supported
    subst supported
    rw [consumedBits_word, if_neg hd]
    rfl

theorem CursorAt.setPC {s : MachineState} {cursor : ℕ} (atCursor : CursorAt s cursor) (pc : Word) :
    CursorAt (s.setPC pc) cursor := by
  unfold CursorAt
  rw [MachineState.getReg_setPC]
  exact atCursor

/-- One specified cursor step re-establishes the invariant at the resulting machine state. -/
theorem transitionState_invariant {s : MachineState} {index : Fin (2 ^ 115)}
    {payload : List Bool} {pk : PublicKey paperParams} {x : graph.Assignment} {cursor : ℕ}
    (inv : NodeState s index payload pk x cursor) (n : Name)
    (bounded : cursor + consumedBits index n ≤ 5248) (result : graph.Assignment × ℕ)
    (supported : result ∈ support (cursorStep index payload x cursor n)) :
    NodeState (transitionState s index n result) index payload pk result.1 result.2 := by
  have other := nodePrelude_other inv.context n x inv.stored
  have value := nodePrelude_value inv.context n cursor inv.atCursor inv.aligned bounded
  have moved := nodePrelude_cursor inv.context n cursor inv.atCursor inv.aligned
  have context := nodePrelude_context inv.context n
  have destination := nodePrelude_destination s n
  have consumed := consumedBits_word index n
  unfold cursorStep at supported
  split_ifs at supported with hd he
  · have he := disclosed_not_evaluated (fixedPositions index) n hd
    rw [mem_support_pure_iff] at supported
    subst supported
    rw [if_pos hd] at value
    rw [if_pos hd] at consumed
    have length := disclosed_length _ n hd
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [transitionState, he, Bool.false_eq_true, if_false]
      exact context.setPC _
    · simp only [transitionState, he, Bool.false_eq_true, if_false]
      exact (other.setPC _).update _ ((memBits_setPC _).mpr value)
    · simp only [transitionState, he, Bool.false_eq_true, if_false, length]
      rw [← consumed]
      exact moved.setPC _
    · have aligned := inv.aligned
      simp only [length]
      omega
  · obtain ⟨y, hy, rfl⟩ := mem_support_map_peel _ _ supported
    rw [runOp_eq] at hy
    rw [if_neg hd] at value
    rw [if_neg hd] at consumed
    have destination' : (((nodePrelude n).eval s).setPC (((nodePrelude n).eval s).pc + 4)).getReg
        .x18 = BitVec.ofNat 64 (slotAddress n) := by
      rw [MachineState.getReg_setPC]
      exact destination
    have frame := nodeResult_frame (((nodePrelude n).eval s).setPC (((nodePrelude n).eval s).pc + 4))
      n y destination'
    refine ⟨?_, ?_, ?_, inv.aligned⟩
    · simp only [transitionState, he, if_true, Function.update_self]
      exact (context.setPC _).frame frame.below (nodeResult_register _ n y .x8 (Or.inl rfl))
    · simp only [transitionState, he, if_true, Function.update_self]
      exact nodeResult_storage _ n x destination' (other.setPC _) ((memBits_setPC _).mpr value) y hy
    · simp only [transitionState, he, if_true, Function.update_self]
      unfold CursorAt
      rw [nodeResult_register _ n y .x9 (Or.inr rfl), MachineState.getReg_setPC]
      rw [consumed, Nat.add_zero] at moved
      exact moved
  · rw [mem_support_pure_iff] at supported
    subst supported
    rw [if_neg hd] at value
    rw [if_neg hd] at consumed
    have he' : evaluated (fixedPositions index) n = false := by simpa using he
    refine ⟨?_, ?_, ?_, inv.aligned⟩
    · simp only [transitionState, he', Bool.false_eq_true, if_false]
      exact context.setPC _
    · simp only [transitionState, he', Bool.false_eq_true, if_false]
      exact (other.setPC _).update _ ((memBits_setPC _).mpr value)
    · simp only [transitionState, he', Bool.false_eq_true, if_false]
      rw [consumed, Nat.add_zero] at moved
      exact moved.setPC _

/-- Executing a node list realizes the specification's sequential reader, then any
continuation established from the final context and storage. -/
theorem runNodes_observe (index : Fin (2 ^ 115)) (payload : List Bool)
    (pk : PublicKey paperParams) (tail : Code)
    (q : graph.Assignment → OracleComp (Spec paperParams) (Option Bool)) (rest : ℕ)
    (continuation : ∀ (t : MachineState) (y : graph.Assignment),
      ExecutionContext t index payload pk → NodeStorage t y → Riscv.CodeAt t t.pc tail →
      ∀ left, rest ≤ left → Riscv.observe left t = q y)
    (nodes : List Name) :
    ∀ (s : MachineState) (x : graph.Assignment) (cursor fuel : ℕ),
      NodeState s index payload pk x cursor →
      cursor + (nodes.map (consumedBits index)).sum ≤ 5248 →
      Riscv.CodeAt s s.pc (nodes.flatMap nodeCode ++ tail) →
      (nodes.flatMap nodeCode).length + rest ≤ fuel →
      Riscv.observe fuel s = runNodes index payload nodes x cursor >>= q := by
  induction nodes with
  | nil =>
    intro s x cursor fuel inv _ located bound
    simp only [runNodes, pure_bind]
    simp only [List.flatMap_nil, List.nil_append, List.length_nil, Nat.zero_add] at located bound
    exact continuation s x inv.context inv.stored located fuel bound
  | cons n ns ih =>
    intro s x cursor fuel inv budget located bound
    have sumCons : ((n :: ns).map (consumedBits index)).sum =
        consumedBits index n + (ns.map (consumedBits index)).sum := by
      simp only [List.map_cons, List.sum_cons]
    have lenCons : ((n :: ns).flatMap nodeCode).length =
        (nodeCode n).length + (ns.flatMap nodeCode).length := by
      simp only [List.flatMap_cons, List.length_append]
    rw [List.flatMap_cons, List.append_assoc] at located
    have boundedNode : cursor + consumedBits index n ≤ 5248 := by
      rw [sumCons] at budget
      omega
    have ready : NodeReady s n :=
      node_ready s n inv.context.positionBase (inv.atCursor.ready (by omega) inv.aligned)
    have afterNode : ∀ next ∈ support (nodeEffect s n),
        ∀ result ∈ support (cursorStep index payload x cursor n),
        next = transitionState s index n result →
        ∀ left, (ns.flatMap nodeCode).length + rest ≤ left →
        Riscv.observe left next = runNodes index payload ns result.1 result.2 >>= q := by
      intro next hn result hr hnext left hleft
      have pcCode := nodeEffect_pc_code s next n ready hn
      subst hnext
      apply ih _ _ _ _ (transitionState_invariant inv n boundedNode result hr)
      · rw [cursorStep_snd index payload x cursor n result hr]
        rw [sumCons] at budget
        omega
      · rw [pcCode.1]
        exact located.append_right.code_eq pcCode.2
      · exact hleft
    have peel : ∀ next ∈ support (nodeEffect s n),
        ∃ result ∈ support (cursorStep index payload x cursor n),
          next = transitionState s index n result := by
      intro next hn
      rw [nodeEffect_eq inv.context n x inv.stored cursor] at hn
      exact mem_support_map_peel _ _ hn
    rw [node_cps s n fuel ((ns.flatMap nodeCode).length + rest)
      (fun next => Riscv.observe ((ns.flatMap nodeCode).length + rest) next)
      located.append_left ready (by rw [lenCons] at bound; omega) ?_]
    · rw [nodeEffect_eq inv.context n x inv.stored cursor, runNodes]
      simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp_apply, pure_bind]
      apply bind_congr_of_forall_mem_support
      intro result hr
      obtain ⟨y, next⟩ := result
      exact afterNode _ (by
        rw [nodeEffect_eq inv.context n x inv.stored cursor, support_map]
        exact ⟨(y, next), hr, rfl⟩) (y, next) hr rfl _ le_rfl
    · intro next hn left hleft
      obtain ⟨result, hr, rfl⟩ := peel next hn
      rw [afterNode _ hn result hr rfl left hleft, afterNode _ hn result hr rfl _ le_rfl]

end OptimalOTS.RiscvUpperProgram.Direct
