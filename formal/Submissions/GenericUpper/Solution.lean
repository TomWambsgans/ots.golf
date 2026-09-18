import Submissions.GenericUpper.ForestAlgorithm

/-! A fully admissible generic oracle algorithm with verification cost at most 106. -/

namespace OptimalOTS.Challenge.GenericUpper

/-- The forest's unchanged key-generation, signing, and verification programs. -/
noncomputable def scheme : AlgorithmScheme paperParams := GenericUpperForest.scheme

/-- Perfect correctness, signing failure at most `2⁻¹²⁸`, and the paper's resource limits. -/
theorem admissible :
    scheme.Admissible AlgorithmScheme.paperLimits (1 / 2 ^ 128) := GenericUpperForest.admissible

/-- 127-bit strong unforgeability in the shared random-oracle experiment. -/
theorem secure : scheme.Secure := GenericUpperForest.secure

/-- A bound for every input and every oracle-answer path, including rejecting inputs. -/
theorem cost : scheme.VerifyCostAtMost 106 := GenericUpperForest.cost

end OptimalOTS.Challenge.GenericUpper
