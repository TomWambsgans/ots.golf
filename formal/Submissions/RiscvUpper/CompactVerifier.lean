import Submissions.RiscvUpper.CompactTree
import Submissions.RiscvUpper.CompactCost
import Submissions.RiscvUpper.IndexRefines
import Submissions.RiscvUpper.DecoderExecution

/-!
# Exact refinement of the compact machine image

The compact image observes exactly the certified raw-signature verifier, preserving every oracle
query, and every accepting run costs at most `cycleBound` cycles: one cycle per executed
instruction, with the 912-bit root hash charged two. The index phase (query, nibble checks and
position stores) costs 271 cycles and the chain phase 4854 cycles on every accepted index.
-/

namespace OptimalOTS.RiscvUpperProgram.Compact

open RiscvZkvm.Rv64 Forest Forest.Name RiscvUpperForest.ForestVerifier OracleComp
open scoped Classical

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
theorem index_take (bits : List Bool) : ofBits 256 (bits.take 256) = ofBits 256 bits := by
  simpa only [List.drop_zero] using
    ofBits_drop_take bits (cap := 256) (start := 0) (len := 256) le_rfl

/-- The specification after the accepted index and wire-length checks. -/
noncomputable def acceptedTail (pk : PublicKey paperParams) (bits : List Bool)
    (answer : BitVec paperParams.hashBits) : OracleComp (Spec paperParams) (Option Bool) :=
  some <$> (if hi : (answer.setWidth paperParams.idxBits).toNat ∈ validSet paperParams then
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
      if Accepted (answer.setWidth 128).toNat ∧ bits.length = 5504 then
        acceptedTail pk bits answer
      else pure (some false)) := by
  unfold directVerify index acceptedTail
  rw [index_take]
  simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp_apply, pure_bind]
  apply bind_congr_of_forall_mem_support
  intro answer _
  by_cases hi : Accepted (answer.setWidth 128).toNat
  · have hi' : (answer.setWidth paperParams.idxBits).toNat ∈ validSet paperParams :=
      (acceptedIdx answer hi).2
    rw [dif_pos hi']
    by_cases hlen : bits.length = 5504
    · rw [if_pos hlen, if_pos ⟨hi, hlen⟩]
    · rw [if_neg hlen, if_neg (fun h => hlen h.2), pure_bind]
      rfl
  · have hi' : ¬ (answer.setWidth paperParams.idxBits).toNat ∈ validSet paperParams :=
      fun h => hi (mem_validSet_accepted h)
    rw [dif_neg hi', if_neg (fun h => hi h.1), pure_bind]
    rfl

theorem image_code : image.code = verifier := rfl

theorem initial_pc (pk : PublicKey paperParams) (m : Message paperParams) (bits : List Bool) :
    (Riscv.initialState image pk m bits).pc = Riscv.codeBase := by
  simp [Riscv.initialState]

set_option allowUnsafeReducibility true
attribute [local reducible] paperParams Forest.graph

theorem verifier_length : verifier.length = 9674 := by decide +kernel

theorem image_valid : image.Valid := by
  refine ⟨?_, ?_, ?_⟩
  · change verifier.length ≤ 262144
    rw [verifier_length]
    norm_num
  · change ([] : List Riscv.Byte).length ≤ 1048576
    simp
  · have checked : verifier.all Riscv.admittedInstruction = true := by decide +kernel
    exact List.all_eq_true.mp checked

theorem image_data : image.data = [] := rfl

theorem image_data_length : image.data.length ≤ 1048576 := by
  rw [image_data]
  simp

theorem CodeAt.at_offset {s t : MachineState} {pc : Word} {first last : List Instr}
    (located : Riscv.CodeAt s pc (first ++ last)) (same : t.code = s.code)
    (hpc : t.pc = pc + BitVec.ofNat 64 (4 * first.length)) : Riscv.CodeAt t t.pc last := by
  rw [hpc]
  exact located.append_right.code_eq same

/-- The reader's node order, split as the machine processes it. -/
theorem order_eq : order = (srcs ++ levelsFrom 0) ++
    ((gcs ++ (ghs ++ gvs)) ++ ((ecs ++ (ehs ++ evs)) ++ [rc, rh])) := by
  rw [order_split, treeNodes_split]
  simp only [List.append_assoc]

/-- The certified accepting-path cycle count. -/
def cycleBound : ℕ := 5513

/-- The index phase and the chain phase are charged their exact executed costs, 271 and 4854
cycles for every accepted index. -/
theorem cost_arith : 4854 + (groups.length +
    (subtrees.length + (root.length + 1 + decision.length))) + 271 = cycleBound := by
  decide +kernel

theorem lengths : indexAndChecks.length + (chains.length +
    (groups.length + (subtrees.length + (root.length + decision.length)))) = 9674 := by
  have h := verifier_length
  simp only [verifier, List.length_append] at h
  omega

/-- The accepted branch of the specification, as the reader over `order`. -/
theorem acceptedTail_eq (pk : PublicKey paperParams) (bits : List Bool) (answer : BitVec 256)
    (hi : (answer.setWidth 128).toNat ∈ validSet paperParams) (hlen : bits.length = 5504) :
    acceptedTail pk bits answer =
      runNodes' ⟨_, hi⟩ (bits.drop 256) order (fun _ => 0) 0 >>= fun r =>
        pure (some (@decide ((r.1 rh.fin).setWidth 128 = pk) (Classical.propDecidable _))) := by
  have hi' : (@BitVec.setWidth paperParams.hashBits paperParams.idxBits answer).toNat ∈
      validSet paperParams := hi
  unfold acceptedTail
  rw [dif_pos hi', if_pos hlen]
  simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp_apply, pure_bind, directReconstruct,
    runNodes_eq_fst]
  try simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp_apply, pure_bind]
  try rfl

/-- The compact image computes exactly the specified verifier within its fuel, and every
accepting run costs at most `cycleBound` cycles. -/
theorem image_refines (pk : PublicKey paperParams) (m : Message paperParams) (bits : List Bool) :
    Riscv.Refines 9674 (Riscv.initialState image pk m bits) (some <$> directVerify pk m bits)
      cycleBound := by
  have located := Riscv.CodeAt.initial image pk m bits image_valid
  rw [image_code, ← initial_pc pk m bits] at located
  change Riscv.CodeAt _ _
    (indexAndChecks ++ chains ++ groups ++ subtrees ++ root ++ decision) at located
  simp only [List.append_assoc] at located
  rw [directVerify_unfold, ← cost_arith]
  apply indexAndChecks_refines image pk m bits image_data_length
    (chains.length + (groups.length + (subtrees.length + (root.length + decision.length)))) 9674
    (fun answer => acceptedTail pk bits answer)
    _ (by have h1 := lengths; have h2 := indexAndChecks_length; omega) located.append_left
    (by rw [lengths])
  intro answer hi hlen left hleft
  show Riscv.Refines left (decodedInput image pk m bits answer) (acceptedTail pk bits answer) _
  rw [acceptedTail_eq pk bits answer (acceptedIdx answer hi).2 hlen, order_eq, runNodes'_append]
  simp only [bind_assoc]
  -- the chains
  have located2 : Riscv.CodeAt (decodedInput image pk m bits answer)
      (decodedInput image pk m bits answer).pc
      (chains ++ (groups ++ (subtrees ++ (root ++ decision)))) := by
    apply CodeAt.at_offset located (decodedInput_code image pk m bits answer)
    rw [decodedInput_pc image pk m bits answer, initial_pc]
  refine Riscv.Refines.mono ?_ (show chainsCost (acceptedIdx answer hi) +
    (groups.length + (subtrees.length + (root.length + 1 + decision.length))) ≤ _ by
      have := chainsCost_le (acceptedIdx answer hi); omega)
  apply chains_refines (acceptedIdx answer hi) (bits.drop 256) pk
    (groups ++ (subtrees ++ (root ++ decision))) _
    (groups.length + (subtrees.length + (root.length + 1 + decision.length)))
    (groups.length + (subtrees.length + (root.length + decision.length))) ?_ _
    (decodedInput_context image pk m bits answer image_data_length hi) _ left located2 hleft
  intro u y cursor1 done1 located3 left2 hleft2
  dsimp only
  rw [runNodes'_append]
  simp only [bind_assoc]
  -- the groups
  apply groups_refines (acceptedIdx answer hi) (bits.drop 256) pk (subtrees ++ (root ++ decision)) _
    (subtrees.length + (root.length + 1 + decision.length))
    (subtrees.length + (root.length + decision.length)) ?_ u y cursor1 left2 done1 located3 hleft2
  intro v z cursor2 done2 located4 left3 hleft3
  dsimp only
  rw [runNodes'_append]
  simp only [bind_assoc]
  -- the subtrees
  apply subtrees_refines (acceptedIdx answer hi) (bits.drop 256) pk (root ++ decision) _
    (root.length + 1 + decision.length) (root.length + decision.length) ?_ v z cursor2 left3 done2
    located4 hleft3
  intro w t cursor3 done3 located5 left4 hleft4
  dsimp only
  -- the root and the decision
  exact rootDecision_refines (acceptedIdx answer hi) (bits.drop 256) pk w t cursor3 left4 done3 located5 hleft4

/--
info: 'OptimalOTS.RiscvUpperProgram.Compact.image_refines' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms image_refines

end OptimalOTS.RiscvUpperProgram.Compact
