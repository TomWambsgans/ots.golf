import OptimalOTS.Algorithm
import OptimalOTS.RiscvMachine

/-!
# RISC-V upper submissions

The signature is its transmitted bit string. The implementation proof identifies the
machine's complete oracle computation with the supplied Lean verifier, preserving queries
and their compression costs. `Implements` requires every execution to terminate, and every
execution, accepting or rejecting, is ranked by cycles.
-/

namespace OptimalOTS.Riscv

open OracleComp

/-- An OTS specification and its assembly image. `fuel` witnesses termination on each input;
it is not a runtime input to the assembly and is not its scored cycle allowance. -/
structure Submission where
  SecretKey : Type
  keygen : OracleComp (Spec paperParams) (PublicKey paperParams × SecretKey)
  sign : SecretKey → Message paperParams → OracleComp (Spec paperParams) (Option (List Bool))
  verify : PublicKey paperParams → Message paperParams → List Bool →
    OracleComp (Spec paperParams) Bool
  image : Image
  fuel : PublicKey paperParams → Message paperParams → List Bool → ℕ

def Submission.scheme (S : Submission) : AlgorithmScheme paperParams where
  SecretKey := S.SecretKey
  Signature := List Bool
  encodeSignature := id
  encodeSignature_injective := Function.injective_id
  keygen := S.keygen
  sign := S.sign
  verify := S.verify

def Submission.run (S : Submission) (pk : PublicKey paperParams) (m : Message paperParams)
    (signature : List Bool) : OracleComp (Spec paperParams) Outcome :=
  execute (S.fuel pk m signature) (initialState S.image pk m signature)

/-- Exact oracle-program refinement. `some` rules out traps and exhausted fuel on every path,
including rejects. The same theorem also preserves the security experiment's query accounting. -/
def Submission.Implements (S : Submission) : Prop :=
  S.image.Valid ∧ ∀ pk m signature,
    Option.map Prod.fst <$> S.run pk m signature = some <$> S.verify pk m signature

/-- Every execution, accepting or rejecting, costs at most `c` cycles. -/
def Submission.CostAtMost (S : Submission) (c : ℕ) : Prop :=
  ∀ pk m signature b cycles, some (b, cycles) ∈ support (S.run pk m signature) → cycles ≤ c

/-- All requirements for one scored RISC-V submission, with the fixed competition budgets. -/
structure Submission.Certificate (S : Submission) (c : ℕ) : Prop where
  admissible : S.scheme.Admissible AlgorithmScheme.paperLimits (1 / 2 ^ 128)
  secure : S.scheme.Secure
  implements : S.Implements
  cost : S.CostAtMost c

end OptimalOTS.Riscv
