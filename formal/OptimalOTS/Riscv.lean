import OptimalOTS.Algorithm
import OptimalOTS.RiscvMachine

/-!
# RISC-V upper submissions

The signature is its transmitted bit string. The implementation proof identifies the
machine's complete oracle computation with the supplied Lean verifier, preserving queries,
randomness, and their compression costs. Every execution terminates; only accepting
executions are ranked by cycles. No sampled benchmark is an admission requirement.
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

/-- Refinement requires termination on every input and every oracle-answer path. -/
theorem Submission.no_fault (S : Submission) (h : S.Implements)
    (pk : PublicKey paperParams) (m : Message paperParams) (signature : List Bool) :
    none ∉ support (S.run pk m signature) := by
  intro fault
  have mapped : none ∈ support (Option.map Prod.fst <$> S.run pk m signature) := by
    rw [support_map]
    exact ⟨none, fault, rfl⟩
  rw [h.2 pk m signature, support_map] at mapped
  obtain ⟨b, _, impossible⟩ := mapped
  cases impossible

/-- A universal bound on accepting runs only. Rejecting runs may take any finite cost. -/
def Submission.AcceptCostAtMost (S : Submission) (c : ℕ) : Prop :=
  ∀ pk m signature cycles, some (true, cycles) ∈ support (S.run pk m signature) → cycles ≤ c

/-- The OTS using the actual machine verifier, with faults interpreted as rejection. -/
def Submission.implementedScheme (S : Submission) : AlgorithmScheme paperParams :=
  { S.scheme with verify := fun pk m signature =>
      (fun result => (result.map Prod.fst).getD false) <$> S.run pk m signature }

/-- Refinement identifies the entire implemented OTS with its proved specification. -/
theorem Submission.implementedScheme_eq (S : Submission) (h : S.Implements) :
    S.implementedScheme = S.scheme := by
  have hv : (fun pk m signature =>
      (fun result => (result.map Prod.fst).getD false) <$> S.run pk m signature) = S.verify := by
    funext pk m signature
    have he := congrArg (fun computation : OracleComp (Spec paperParams) (Option Bool) =>
      (fun result => result.getD false) <$> computation) (h.2 pk m signature)
    simpa [Functor.map_map, Function.comp_def] using he
  unfold Submission.implementedScheme Submission.scheme
  dsimp only
  rw [hv]

/-- The 127-bit proof applies to the implemented verifier with its actual hash-query costs. -/
theorem Submission.implemented_secure (S : Submission) (h : S.Implements)
    (secure : S.scheme.Secure) : S.implementedScheme.Secure := by
  rwa [S.implementedScheme_eq h]

/-- Correctness, signing availability, and the size and resource limits also transfer. -/
theorem Submission.implemented_admissible (S : Submission) (h : S.Implements)
    (admissible : S.scheme.Admissible AlgorithmScheme.paperLimits (1 / 2 ^ 128)) :
    S.implementedScheme.Admissible AlgorithmScheme.paperLimits (1 / 2 ^ 128) := by
  rwa [S.implementedScheme_eq h]

/-- All requirements for one scored RISC-V submission, with the fixed competition budgets. -/
structure Submission.Certificate (S : Submission) (c : ℕ) : Prop where
  admissible : S.scheme.Admissible AlgorithmScheme.paperLimits (1 / 2 ^ 128)
  secure : S.scheme.Secure
  implements : S.Implements
  cost : S.AcceptCostAtMost c

end OptimalOTS.Riscv
