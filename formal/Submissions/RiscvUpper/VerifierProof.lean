import Submissions.RiscvUpper.DirectCost
import Submissions.RiscvUpper.IndexExecution
import Submissions.RiscvUpper.DecoderExecution
import Submissions.RiscvUpper.ReconstructionExecution
import Submissions.RiscvUpper.DecisionProof

/-!
# Exact refinement of the direct machine image

The complete machine observation equals the certified raw-signature verifier, preserving
every oracle query. Every input terminates within the fixed fuel, including rejections.
-/

namespace OptimalOTS.RiscvUpperProgram.Direct

open RiscvZkvm.Rv64 Forest Forest.Name RiscvUpperForest.ForestVerifier OracleComp
open scoped Classical

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option allowUnsafeReducibility true
attribute [local reducible] Forest.graph
attribute [local irreducible] Forest.fixedPositions Forest.fixedDigits

theorem CodeAt.at_offset {s t : MachineState} {pc : Word} {first last : List Instr}
    (located : Riscv.CodeAt s pc (first ++ last)) (same : t.code = s.code)
    (hpc : t.pc = pc + BitVec.ofNat 64 (4 * first.length)) : Riscv.CodeAt t t.pc last := by
  rw [hpc]
  exact located.append_right.code_eq same

/-- The fixed cursor literal names the first disclosed word. -/
theorem cursor_literal :
    literalValue (Riscv.signatureBase.toNat + 32) =
      Riscv.signatureBase + 32 + BitVec.ofNat 64 (0 / 8) := by decide +kernel

/-- Reconstruction from cleared storage realizes the specification's direct reconstruction. -/
theorem reconstruction_continuation (index : Fin (2 ^ 115)) (payload : List Bool)
    (pk : PublicKey paperParams) (s : MachineState)
    (context : ExecutionContext s index payload pk) (stored : NodeStorage s (fun _ => 0))
    (located : Riscv.CodeAt s s.pc (reconstruction ++ decision)) (rest fuel : ℕ)
    (bound : reconstruction.length + rest ≤ fuel)
    (q : graph.Assignment → OracleComp (Spec paperParams) (Option Bool))
    (continuation : ∀ (t : MachineState) (y : graph.Assignment),
      ExecutionContext t index payload pk → NodeStorage t y → Riscv.CodeAt t t.pc decision →
      ∀ left, rest ≤ left → Riscv.observe left t = q y) :
    Riscv.observe fuel s = directReconstruct index payload >>= q := by
  let init := constant .x9 (Riscv.signatureBase.toNat + 32)
  let s' := init.foldl execInstrBr s
  have ready : Riscv.LinearReady s init := constant_ready s .x9 _
  have parts : reconstruction ++ decision = init ++ (order.flatMap nodeCode ++ decision) := by
    simp only [reconstruction, init, List.append_assoc]
  rw [parts] at located
  have lengths : reconstruction.length = init.length + (order.flatMap nodeCode).length := by
    simp only [reconstruction, init, List.length_append]
  rw [show fuel = init.length + (fuel - init.length) by omega,
    Riscv.observe_linear _ s init located.append_left ready]
  change Riscv.observe (fuel - init.length) s' = _
  have frame : FrameBelow s s' := fun addr _ => congrFun (constant_mem s .x9 _) addr
  have base : s'.getReg .x8 = s.getReg .x8 := constant_preserves s .x9 .x8 _ (by decide)
  have inv : NodeState s' index payload pk (fun _ => 0) 0 := by
    refine ⟨context.frame frame base, ?_, ?_, rfl⟩
    · intro n
      exact memBits_of_mem_eq (constant_mem s .x9 _) (stored n)
    · unfold CursorAt
      change (init.foldl execInstrBr s).getReg .x9 = _
      rw [constant_value s .x9 _ (by decide), cursor_literal]
  have located' : Riscv.CodeAt s' s'.pc (order.flatMap nodeCode ++ decision) :=
    CodeAt.at_offset located (Riscv.fold_code s init) (constant_pc s .x9 _)
  exact runNodes_observe index payload pk decision q rest continuation order s' (fun _ => 0) 0
    (fuel - init.length) inv (by rw [total_consumed]) located' (by omega)

theorem image_data : image.data = tableData := rfl

theorem image_code : image.code = verifier := rfl

theorem index_take (bits : List Bool) : ofBits 256 (bits.take 256) = ofBits 256 bits := by
  simpa only [List.drop_zero] using
    ofBits_drop_take bits (cap := 256) (start := 0) (len := 256) le_rfl

/-- The specification after the accepted index and wire-length checks. -/
noncomputable def acceptedTail (pk : PublicKey paperParams) (bits : List Bool)
    (answer : BitVec paperParams.hashBits) : OracleComp (Spec paperParams) (Option Bool) :=
  some <$> (if hi : (answer.setWidth paperParams.idxBits).toNat < paperParams.numSets then
      if bits.length = 5504 then (do
        let y ← directReconstruct ⟨_, hi⟩ (bits.drop 256)
        return decide ((y rh.fin).setWidth 128 = pk))
      else return false
    else return false)

/-- The specified verifier, expressed on the first oracle answer. -/
theorem directVerify_unfold (pk : PublicKey paperParams) (m : Message paperParams)
    (bits : List Bool) :
    some <$> directVerify pk m bits = (do
      let answer ← hash paperParams (m ++ ofBits 256 bits)
      if (answer.setWidth 128).toNat < 2 ^ 115 ∧ bits.length = 5504 then
        acceptedTail pk bits answer
      else pure (some false)) := by
  unfold directVerify index acceptedTail
  rw [index_take]
  simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp_apply, pure_bind]
  apply bind_congr_of_forall_mem_support
  intro answer _
  by_cases hi : (answer.setWidth 128).toNat < 2 ^ 115
  · have hi' : (answer.setWidth paperParams.idxBits).toNat < paperParams.numSets := hi
    rw [dif_pos hi']
    by_cases hlen : bits.length = 5504
    · rw [if_pos hlen, if_pos ⟨hi, hlen⟩]
    · rw [if_neg hlen, if_neg (fun h => hlen h.2), pure_bind]
      rfl
  · have hi' : ¬ (answer.setWidth paperParams.idxBits).toNat < paperParams.numSets := hi
    rw [dif_neg hi', if_neg (fun h => hi h.1), pure_bind]
    rfl

/-- The direct image computes exactly the specified verifier and terminates on every input,
for any fuel of at least the instruction count. -/
theorem image_observe (pk : PublicKey paperParams) (m : Message paperParams) (bits : List Bool)
    (fuel : ℕ) (enough : 114557 ≤ fuel) :
    Riscv.observe fuel (Riscv.initialState image pk m bits) = some <$> directVerify pk m bits := by
  have total : indexAndChecks.length + (decodePositions.length +
      (reconstruction.length + decision.length)) = 114557 := by
    have h := verifier_length
    simp only [verifier, List.length_append] at h
    omega
  have located := Riscv.CodeAt.initial image pk m bits image_valid
  rw [image_code, ← initial_pc pk m bits] at located
  change Riscv.CodeAt _ _ (indexAndChecks ++ decodePositions ++ reconstruction ++ decision) at located
  rw [List.append_assoc, List.append_assoc] at located
  rw [directVerify_unfold]
  apply indexAndChecks_continuation image pk m bits image_valid.2.1
    (decodePositions.length + (reconstruction.length + decision.length)) fuel
    (fun answer => acceptedTail pk bits answer) located.append_left (by omega)
  intro answer hi hlen left hleft
  have hi' : (@BitVec.setWidth paperParams.hashBits paperParams.idxBits answer).toNat <
      paperParams.numSets := hi
  show Riscv.observe left _ = acceptedTail pk bits answer
  unfold acceptedTail
  rw [dif_pos hi', if_pos hlen]
  simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp_apply, pure_bind]
  have checked_pc := checkedInput_pc image pk m bits answer
  have located1 : Riscv.CodeAt
      (checkedIndexState (Riscv.writeHash (indexInputState image pk m bits) answer))
      (checkedIndexState (Riscv.writeHash (indexInputState image pk m bits) answer)).pc
      (decodePositions ++ (reconstruction ++ decision)) := by
    apply CodeAt.at_offset located (checkedInput_code image pk m bits answer)
    rw [checked_pc, initial_pc, indexAndChecks_length]
    rfl
  apply decodePositions_continuation image pk m bits answer image_data hi
    (reconstruction.length + decision.length) left _ located1.append_left (by omega)
  intro left' hleft'
  have located2 : Riscv.CodeAt (decodedInput image pk m bits answer)
      (decodedInput image pk m bits answer).pc (reconstruction ++ decision) := by
    apply CodeAt.at_offset located1 (decodedInput_code image pk m bits answer)
    rw [decodedInput_pc image pk m bits answer image_data hi, checked_pc,
      indexAndChecks_length, Nat.mul_add, BitVec.ofNat_add, ← BitVec.add_assoc]
    try rfl
  apply reconstruction_continuation ⟨_, hi'⟩ (bits.drop 256) pk _
    (decodedInput_context image pk m bits answer image_data hi)
    (decodedInput_nodes image pk m bits answer image_data hi) located2 decision.length left'
    (by omega)
  intro t y context stored located3 left'' hleft''
  have root : MemBits t (BitVec.ofNat 64 (slotAddress rh)) ((y rh.fin).setWidth 128) := stored.low rh
  rw [decision_observe t ((y rh.fin).setWidth 128) pk left'' located3 root context.publicKey hleft'']
  exact congrArg (fun b => pure (some b)) (decide_eq_decide.mpr Iff.rfl)

/--
info: 'OptimalOTS.RiscvUpperProgram.Direct.image_observe' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms image_observe

end OptimalOTS.RiscvUpperProgram.Direct
