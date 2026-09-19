import OptimalOTS.OracleAlgorithm
import OptimalOTS.RiscvMachine

/-!
# RISC-V upper submissions

A submission is an oracle-algorithm scheme together with a machine image. Its certificate proves
that the image performs exactly the Lean verifier's oracle computation (the same queries and the
same decision) on every input, and bounds the cycles of every execution, accepting or rejecting.
-/

namespace OptimalOTS.Riscv

open OracleComp

/-- An OTS and its machine image. `fuel` bounds the instructions run on each input, witnessing
termination; it is neither a machine input nor the score. -/
structure Submission where
  scheme : OracleAlgorithm.Scheme
  image : Image
  fuel : PublicKey → Message → List Bool → ℕ

/-- The machine run on one input, from the loader's initial state. -/
def Submission.run (S : Submission) (pk : PublicKey) (m : Message) (signature : List Bool) :
    OracleComp Spec Outcome :=
  execute (S.fuel pk m signature) (initialState S.image pk m signature)

/-- The image is valid and, on every input and every oracle-answer path, the machine halts with
the Lean verifier's decision after making the same oracle queries. Traps and exhausted fuel are
ruled out, on accepting and rejecting inputs alike. -/
def Submission.Implements (S : Submission) : Prop :=
  S.image.Valid ∧ ∀ pk m signature,
    Option.map Prod.fst <$> S.run pk m signature = some <$> S.scheme.verify pk m signature

/-- Every execution, accepting or rejecting, takes at most `c` cycles. -/
def Submission.CyclesAtMost (S : Submission) (c : ℕ) : Prop :=
  ∀ pk m signature b cycles, some (b, cycles) ∈ support (S.run pk m signature) → cycles ≤ c

/-- The certificate for claim `c`: the OTS is admissible and secure, the image implements its
verifier, and every execution takes at most `c` cycles. -/
structure Submission.Certificate (S : Submission) (c : ℕ) : Prop where
  admissible : S.scheme.Admissible
  secure : S.scheme.Secure
  implements : S.Implements
  cycles : S.CyclesAtMost c

end OptimalOTS.Riscv
