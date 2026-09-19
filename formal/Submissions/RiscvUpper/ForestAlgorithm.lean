import Submissions.RiscvUpper.Resources
import Submissions.RiscvUpper.Main
import Submissions.RiscvUpper.Correctness
import Submissions.RiscvUpper.Availability

/-!
# The verified forest under the generic algorithm interface

The forest satisfies the generic challenge: perfect correctness, signing failure at most
`2⁻¹²⁸`, 127-bit strong security, and verification within 186 compressions on every path.
-/

open OracleSpec OracleComp ENNReal
noncomputable section
open scoped Classical

namespace OptimalOTS.RiscvUpperForest

attribute [local irreducible] Forest.forestScheme
attribute [local irreducible] GScheme.sign GScheme.signLoop
attribute [local irreducible] AlgorithmScheme.Secure AlgorithmScheme.VerifyCostAtMost
  AlgorithmScheme.KeygenCostAtMost AlgorithmScheme.SignCostAtMost
  AlgorithmScheme.SignatureSizeAtMost AlgorithmScheme.RejectsOversized

def scheme : AlgorithmScheme paperParams := Forest.forestScheme.toAlgorithm

theorem experiment_eq (A : scheme.Adversary) :
    scheme.experiment A =
      GScheme.experiment Forest.forestScheme
        (AlgorithmAdapter.toDAGAdversary Forest.forestScheme A) :=
  AlgorithmAdapter.experiment_eq Forest.forestScheme A

theorem secure : scheme.Secure :=
  (AlgorithmAdapter.secure_iff Forest.forestScheme).2 Forest.forestScheme_secure

/-- This bound covers all public keys, messages and signatures, including rejecting inputs. -/
theorem cost : scheme.VerifyCostAtMost 186 := by
  apply AlgorithmAdapter.verifyCost Forest.forestScheme (v := 185) (by decide)
  intro i
  have h := Forest.forestScheme_verifyCost i
  change 1 + Forest.forestScheme.graph.reconstructCost (Forest.forestScheme.sets i) = 186 at h
  omega

theorem keygen_cost : scheme.KeygenCostAtMost AlgorithmScheme.paperLimits.keygenCost :=
  AlgorithmAdapter.keygenCost Forest.forestScheme

theorem sign_cost : scheme.SignCostAtMost AlgorithmScheme.paperLimits.signCost :=
  AlgorithmAdapter.signCost Forest.forestScheme (by decide)

theorem signature_size : scheme.SignatureSizeAtMost AlgorithmScheme.paperLimits.signatureBits :=
  AlgorithmAdapter.signatureSize Forest.forestScheme

theorem rejects_oversized : scheme.RejectsOversized AlgorithmScheme.paperLimits.signatureBits :=
  AlgorithmAdapter.rejectsOversized Forest.forestScheme

/-- Every honestly returned signature verifies under the same oracle. -/
theorem correct : scheme.Correct := GenericCorrectness.correct Forest.forestScheme

/-- Signing succeeds except with probability at most `2⁻¹²⁸` for every public-key-dependent message. -/
theorem signing_failure : scheme.SigningFailureAtMost (1 / 2 ^ 128) :=
  GenericAvailability.signingFailure

/-- All generic admission requirements, with the challenge's fixed failure allowance. -/
theorem admissible : scheme.Admissible AlgorithmScheme.paperLimits (1 / 2 ^ 128) where
  failure_lt_one := by norm_num
  correct := correct
  signingFailure := signing_failure
  signatureSize := signature_size
  rejectsOversized := rejects_oversized
  keygenCost := keygen_cost
  signCost := sign_cost

/-- A complete admissible, strongly secure, 186-compression construction. -/
theorem certificate :
    scheme.Admissible AlgorithmScheme.paperLimits (1 / 2 ^ 128) ∧
    scheme.Secure ∧ scheme.VerifyCostAtMost 186 :=
  ⟨admissible, secure, cost⟩

/--
info: 'OptimalOTS.RiscvUpperForest.certificate' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms certificate

end OptimalOTS.RiscvUpperForest
