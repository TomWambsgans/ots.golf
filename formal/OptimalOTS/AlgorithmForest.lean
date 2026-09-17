import OptimalOTS.AlgorithmResources
import Submissions.Upper.Main

/-!
# The verified forest under the generic algorithm interface

The DAG forest retains its 106-compression verification bound and 127-bit strong security.
This certificate also establishes size and honest-party cost bounds. Generic admission still
requires correctness and signing-availability proofs, and a pinned generic upper challenge.
-/

open OracleSpec OracleComp ENNReal
noncomputable section
open scoped Classical

namespace OptimalOTS.AlgorithmForest

attribute [local irreducible] Forest.forestScheme
attribute [local irreducible] Scheme.sign Scheme.signLoop
attribute [local irreducible] AlgorithmScheme.Secure AlgorithmScheme.VerifyCostAtMost
  AlgorithmScheme.KeygenCostAtMost AlgorithmScheme.SignCostAtMost
  AlgorithmScheme.SignatureSizeAtMost AlgorithmScheme.RejectsOversized

def scheme : AlgorithmScheme paperParams := Forest.forestScheme.toAlgorithm

theorem experiment_eq (A : scheme.Adversary) :
    scheme.experiment A =
      OptimalOTS.experiment Forest.forestScheme
        (AlgorithmAdapter.toDAGAdversary Forest.forestScheme A) :=
  AlgorithmAdapter.experiment_eq Forest.forestScheme A

theorem secure : scheme.Secure :=
  (AlgorithmAdapter.secure_iff Forest.forestScheme).2 Forest.forestScheme_secure

/-- This bound covers all public keys, messages and signatures, including rejecting inputs. -/
theorem cost : scheme.VerifyCostAtMost 106 := by
  apply AlgorithmAdapter.verifyCost Forest.forestScheme (v := 105) (by decide)
  intro i
  have h := Forest.forestScheme_verifyCost i
  change 1 + Forest.forestScheme.graph.reconstructCost (Forest.forestScheme.sets i) = 106 at h
  omega

theorem keygen_cost : scheme.KeygenCostAtMost AlgorithmScheme.paperLimits.keygenCost :=
  AlgorithmAdapter.keygenCost Forest.forestScheme

theorem sign_cost : scheme.SignCostAtMost AlgorithmScheme.paperLimits.signCost :=
  AlgorithmAdapter.signCost Forest.forestScheme (by decide)

theorem signature_size : scheme.SignatureSizeAtMost AlgorithmScheme.paperLimits.signatureBits :=
  AlgorithmAdapter.signatureSize Forest.forestScheme

theorem rejects_oversized : scheme.RejectsOversized AlgorithmScheme.paperLimits.signatureBits :=
  AlgorithmAdapter.rejectsOversized Forest.forestScheme

/-- Security, cost, and size bounds for the adapter. This does not assert `Admissible`. -/
theorem certificate : scheme.Secure ∧ scheme.VerifyCostAtMost 106 ∧
    scheme.KeygenCostAtMost 1024 ∧ scheme.SignCostAtMost (2 ^ 21) ∧
    scheme.SignatureSizeAtMost 5504 ∧ scheme.RejectsOversized 5504 :=
  ⟨secure, cost, keygen_cost, sign_cost, signature_size, rejects_oversized⟩

/--
info: 'OptimalOTS.AlgorithmForest.certificate' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms certificate

end OptimalOTS.AlgorithmForest
