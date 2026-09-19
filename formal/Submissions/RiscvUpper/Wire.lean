import Submissions.RiscvUpper.ForestAlgorithm
import Submissions.RiscvUpper.WireAdapter

/-! The fixed-layout forest on the raw signature bit strings loaded by the machine. -/

open OracleComp ENNReal
noncomputable section
open scoped Classical

set_option linter.constructorNameAsVariable false

namespace OptimalOTS.RiscvUpperForest.Wire

attribute [local irreducible] validSet numValid

def decode (bits : List Bool) : Signature paperParams :=
  (ofBits 128 (bits.take 128), bits.drop 128)

theorem decode_encode (σ : Signature paperParams) :
    decode (AlgorithmAdapter.encodeSignature σ) = σ := by
  rcases σ with ⟨nonce, payload⟩
  simp only [decode, AlgorithmAdapter.encodeSignature]
  have hn : (toBits nonce).length = 128 := length_toBits nonce
  simp [← hn]
  exact Prod.ext (ofBits_toBits nonce) rfl

theorem encode_decode (bits : List Bool) (hlen : 128 ≤ bits.length) :
    AlgorithmAdapter.encodeSignature (decode bits) = bits := by
  change toBits (ofBits 128 (bits.take 128)) ++ bits.drop 128 = bits
  rw [toBits_ofBits _ (by simp [hlen]), List.take_append_drop]

theorem reveal_positive (i : Idx paperParams) :
    0 < Forest.forestScheme.graph.revealBits (Forest.forestScheme.sets i) := by
  change 0 < Forest.graph.revealBits (Forest.fins (Forest.setsName i))
  rw [Forest.revealBits_eq]
  have present : Forest.Name.ev 5 ∈ Forest.setsName i := by
    change Forest.Name.ev 5 ∈ Forest.cutOf (Forest.fixedChoice i)
    rw [Forest.ev_mem_cutOf_iff']
    change 5 ∈ Forest.fixedE
    decide
  have bound := Finset.single_le_sum (s := Forest.setsName i)
    (f := fun n => n.len) (fun _ _ => Nat.zero_le _) present
  have len : (Forest.Name.ev 5).len = 128 := rfl
  rw [len] at bound
  omega

theorem accepted_payload_positive (pk : PublicKey paperParams) (m : Message paperParams)
    (σ : Signature paperParams) (accepted : true ∈ support (Forest.forestScheme.verify pk m σ)) :
    0 < σ.2.length := by
  rw [GScheme.verify, support_bind] at accepted
  simp only [Set.mem_iUnion] at accepted
  obtain ⟨i, _, accepted⟩ := accepted
  split_ifs at accepted with hi hlen
  · rw [hlen]
    exact reveal_positive ⟨i, hi⟩
  · simp at accepted
  · simp at accepted

theorem canonical (pk : PublicKey paperParams) (m : Message paperParams) (bits : List Bool)
    (accepted : true ∈ support (RiscvUpperForest.scheme.verify pk m (decode bits))) :
    RiscvUpperForest.scheme.encodeSignature (decode bits) = bits := by
  have positive := accepted_payload_positive pk m (decode bits) accepted
  have hlen : 128 ≤ bits.length := by
    change 0 < (bits.drop 128).length at positive
    rw [List.length_drop] at positive
    omega
  exact encode_decode bits hlen

def scheme : AlgorithmScheme paperParams := WireAdapter.scheme RiscvUpperForest.scheme decode

theorem secure : scheme.Secure :=
  WireAdapter.secure RiscvUpperForest.scheme decode decode_encode canonical RiscvUpperForest.secure

theorem admissible : scheme.Admissible AlgorithmScheme.paperLimits (1 / 2 ^ 128) :=
  WireAdapter.admissible RiscvUpperForest.scheme decode decode_encode canonical
    AlgorithmScheme.paperLimits (1 / 2 ^ 128) RiscvUpperForest.admissible

theorem cost : scheme.VerifyCostAtMost 186 :=
  WireAdapter.verifyCost RiscvUpperForest.scheme decode 186 RiscvUpperForest.cost

/-- A complete OTS certificate on its transmitted signature bits. -/
theorem certificate : scheme.Admissible AlgorithmScheme.paperLimits (1 / 2 ^ 128) ∧
    scheme.Secure ∧ scheme.VerifyCostAtMost 186 := ⟨admissible, secure, cost⟩

/--
info: 'OptimalOTS.RiscvUpperForest.Wire.certificate' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms certificate

end OptimalOTS.RiscvUpperForest.Wire
