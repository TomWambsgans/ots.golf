import OptimalOTS.Algorithm
import OptimalOTS.RiscvMachine

/-!
# RISC-V upper submissions

A submission is an OTS whose signatures are bit strings, together with a machine image. Its
certificate proves that the image performs exactly the Lean verifier's oracle computation (the
same queries and the same decision) on every input, and bounds the cycles of every execution,
accepting or rejecting.
-/

namespace OptimalOTS.Riscv

open OracleComp

/-- An OTS and its machine image. `fuel` bounds the instructions run on each input, witnessing
termination; it is neither a machine input nor the score. -/
structure Submission where
  SecretKey : Type
  keygen : OracleComp (Spec paperParams) (PublicKey paperParams × SecretKey)
  sign : SecretKey → Message paperParams → OracleComp (Spec paperParams) (Option (List Bool))
  verify : PublicKey paperParams → Message paperParams → List Bool →
    OracleComp (Spec paperParams) Bool
  image : Image
  fuel : PublicKey paperParams → Message paperParams → List Bool → ℕ

/-- The submission as an algorithm scheme; its signature encoding is the identity. -/
def Submission.scheme (S : Submission) : AlgorithmScheme paperParams where
  SecretKey := S.SecretKey
  Signature := List Bool
  encodeSignature := id
  encodeSignature_injective := Function.injective_id
  keygen := S.keygen
  sign := S.sign
  verify := S.verify

/-- The machine run on one input, from the loader's initial state. -/
def Submission.run (S : Submission) (pk : PublicKey paperParams) (m : Message paperParams)
    (signature : List Bool) : OracleComp (Spec paperParams) Outcome :=
  execute (S.fuel pk m signature) (initialState S.image pk m signature)

/-- The image is valid and, on every input and every oracle-answer path, the machine halts with
the Lean verifier's decision after making the same oracle queries. Traps and exhausted fuel are
ruled out, on accepting and rejecting inputs alike. -/
def Submission.Implements (S : Submission) : Prop :=
  S.image.Valid ∧ ∀ pk m signature,
    Option.map Prod.fst <$> S.run pk m signature = some <$> S.verify pk m signature

/-- Every execution, accepting or rejecting, costs at most `c` cycles. -/
def Submission.CostAtMost (S : Submission) (c : ℕ) : Prop :=
  ∀ pk m signature b cycles, some (b, cycles) ∈ support (S.run pk m signature) → cycles ≤ c

/-- The certificate for claim `c`: the OTS is admissible and secure with the competition's
limits, the image implements its verifier, and every execution costs at most `c` cycles. -/
structure Submission.Certificate (S : Submission) (c : ℕ) : Prop where
  admissible : S.scheme.Admissible AlgorithmScheme.paperLimits (1 / 2 ^ 128)
  secure : S.scheme.Secure
  implements : S.Implements
  cost : S.CostAtMost c

end OptimalOTS.Riscv
