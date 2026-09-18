import Submissions.GenericUpper.Solution

/-! Compatibility names for the complete generic upper certificate. The submission root
contains all proofs of correctness, availability, security, and resource bounds. -/

namespace OptimalOTS.AlgorithmForest

attribute [local irreducible] Forest.forestScheme
attribute [local irreducible] AlgorithmScheme.SignCostAtMost AlgorithmScheme.SignatureSizeAtMost

noncomputable abbrev scheme := GenericUpperForest.scheme

theorem experiment_eq (A : scheme.Adversary) :
    scheme.experiment A = OptimalOTS.experiment Forest.forestScheme
      (AlgorithmAdapter.toDAGAdversary Forest.forestScheme A) := GenericUpperForest.experiment_eq A

theorem correct : scheme.Correct := GenericUpperForest.correct
theorem signing_failure : scheme.SigningFailureAtMost (1 / 2 ^ 128) :=
  GenericUpperForest.signing_failure
theorem admissible : scheme.Admissible AlgorithmScheme.paperLimits (1 / 2 ^ 128) :=
  GenericUpperForest.admissible
theorem secure : scheme.Secure := GenericUpperForest.secure
theorem cost : scheme.VerifyCostAtMost 106 := GenericUpperForest.cost
theorem keygen_cost : scheme.KeygenCostAtMost AlgorithmScheme.paperLimits.keygenCost :=
  GenericUpperForest.keygen_cost
theorem sign_cost : scheme.SignCostAtMost AlgorithmScheme.paperLimits.signCost :=
  GenericUpperForest.sign_cost
theorem signature_size : scheme.SignatureSizeAtMost AlgorithmScheme.paperLimits.signatureBits :=
  GenericUpperForest.signature_size
theorem rejects_oversized : scheme.RejectsOversized AlgorithmScheme.paperLimits.signatureBits :=
  GenericUpperForest.rejects_oversized

theorem certificate :
    scheme.Admissible AlgorithmScheme.paperLimits (1 / 2 ^ 128) ∧
    scheme.Secure ∧ scheme.VerifyCostAtMost 106 := GenericUpperForest.certificate

end OptimalOTS.AlgorithmForest
