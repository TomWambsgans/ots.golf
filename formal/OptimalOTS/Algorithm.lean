import OptimalOTS.Statement

/-!
# Generic oracle algorithms for one-time signatures

This interface defines the generic lower track and the foundation for a future upper-track contract.
The algorithms share exactly the existing bare oracle and cost model. There is no graph,
disclosure family, mandatory nonce, or mandatory index query. A scheme supplies its signature
representation and an injective serialization; the size bounds below count the serialized bits.

`Secure` alone is not an admissibility condition. Correctness, signing availability, output size,
and honest-party cost bounds are required by the generic lower track and must also be required
before opening generic upper submissions. The lower challenge pins signing failure at one half.
-/

open OracleSpec OracleComp ENNReal
noncomputable section
open scoped Classical

namespace OptimalOTS

/-- Three arbitrary terminating oracle programs, with an explicit wire representation. -/
structure AlgorithmScheme (P : Params) where
  SecretKey : Type
  Signature : Type
  encodeSignature : Signature → List Bool
  encodeSignature_injective : Function.Injective encodeSignature
  keygen : OracleComp (Spec P) (PublicKey P × SecretKey)
  sign : SecretKey → Message P → OracleComp (Spec P) (Option Signature)
  verify : PublicKey P → Message P → Signature → OracleComp (Spec P) Bool

namespace AlgorithmScheme

variable {P : Params}

/-- The attacker has the same two-stage access as in the DAG experiment. -/
structure Adversary (S : AlgorithmScheme P) where
  State : Type
  choose : PublicKey P → OracleComp (Spec P) (Message P × State)
  forge : State → Option S.Signature → OracleComp (Spec P) (Message P × S.Signature)

/-- Strong unforgeability, including key generation, signing and final verification. -/
def experiment (S : AlgorithmScheme P) (A : S.Adversary) : OracleComp (Spec P) Bool := do
  let (pk, sk) ← S.keygen
  let (m₁, st) ← A.choose pk
  let σ₁ ← S.sign sk m₁
  let (m₂, σ₂) ← A.forge st σ₁
  let ok ← S.verify pk m₂ σ₂
  return ok && decide (σ₁.map (fun s => (m₁, s)) ≠ some (m₂, σ₂))

/-- Exactly the existing total-cost security requirement, with generic honest algorithms. -/
def Secure (S : AlgorithmScheme P) : Prop :=
  ∀ (A : S.Adversary) (B : ℕ), CostAtMost P (S.experiment A) B →
    probTrue P (S.experiment A) < (B : ℝ≥0∞) / 2 ^ P.securityBits

/-- Verification must obey the bound on every input and every execution path, including rejects. -/
def VerifyCostAtMost (S : AlgorithmScheme P) (c : ℕ) : Prop :=
  ∀ pk m σ, CostAtMost P (S.verify pk m σ) c

def KeygenCostAtMost (S : AlgorithmScheme P) (b : ℕ) : Prop := CostAtMost P S.keygen b

def SignCostAtMost (S : AlgorithmScheme P) (b : ℕ) : Prop :=
  ∀ sk m, CostAtMost P (S.sign sk m) b

/-- All possible returned signatures fit on the wire; no uncharged fields are hidden in the type. -/
def SignatureSizeAtMost (S : AlgorithmScheme P) (n : ℕ) : Prop :=
  ∀ sk m σ, some σ ∈ support (S.sign sk m) → (S.encodeSignature σ).length ≤ n

/-- An oversized signature is always rejected, for every sequence of oracle answers. -/
def RejectsOversized (S : AlgorithmScheme P) (n : ℕ) : Prop :=
  ∀ pk m σ, n < (S.encodeSignature σ).length → true ∉ support (S.verify pk m σ)

/-- Honest signing and verification under the same oracle. The message may depend on the public key. -/
def honestExperiment (S : AlgorithmScheme P) (message : PublicKey P → Message P) :
    OracleComp (Spec P) Bool := do
  let (pk, sk) ← S.keygen
  let m := message pk
  let σ ← S.sign sk m
  match σ with
  | none => return false
  | some s => S.verify pk m s

/-- Honest signatures never fail verification; signing may separately return `none`. -/
def Correct (S : AlgorithmScheme P) : Prop := ∀ message : PublicKey P → Message P,
  probTrue P (do
    let (pk, sk) ← S.keygen
    let m := message pk
    let σ ← S.sign sk m
    match σ with
    | none => return false
    | some s => return !(← S.verify pk m s)) = 0

/-- Availability for every public-key-dependent message choice, measured from honest key generation.
This does not promise availability after arbitrary adversarial oracle preprocessing. -/
def SigningFailureAtMost (S : AlgorithmScheme P) (ε : ℝ≥0∞) : Prop :=
  ∀ message : PublicKey P → Message P,
  probTrue P (do
    let (pk, sk) ← S.keygen
    return (← S.sign sk (message pk)).isNone) ≤ ε

/-- Resource limits separate from any DAG's nonce/index/disclosure-family parameters. -/
structure Limits where
  signatureBits : ℕ
  keygenCost : ℕ
  signCost : ℕ

/-- The present sizes and honest-party budgets, expressed without a mandatory nonce format. -/
def paperLimits : Limits where
  signatureBits := 5504
  keygenCost := 1024
  signCost := 2 ^ 21

/-- Generic admissibility, required in addition to security. The lower challenge pins the explicit
signing-failure allowance at one half; stricter future upper allowances are covered by that class. -/
structure Admissible (S : AlgorithmScheme P) (L : Limits) (ε : ℝ≥0∞) : Prop where
  failure_lt_one : ε < 1
  correct : S.Correct
  signingFailure : S.SigningFailureAtMost ε
  signatureSize : S.SignatureSizeAtMost L.signatureBits
  rejectsOversized : S.RejectsOversized L.signatureBits
  keygenCost : S.KeygenCostAtMost L.keygenCost
  signCost : S.SignCostAtMost L.signCost

end AlgorithmScheme
end OptimalOTS
