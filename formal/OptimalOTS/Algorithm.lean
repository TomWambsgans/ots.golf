import OptimalOTS.Statement

/-!
# Generic oracle algorithms for one-time signatures

The interface for generic lower and upper submissions. All parties
share the bare random oracle and its compression cost. Deterministic computation and private
randomness are free.

Public keys and messages have the lengths in `P`. Signatures have an injective bit-string encoding.
`Admissible` fixes correctness, signing availability, signature size, and honest-party cost limits;
security is separate. Both algorithm challenges require signing failure at most `2⁻¹²⁸`.
-/

open OracleSpec OracleComp ENNReal
noncomputable section
open scoped Classical

namespace OptimalOTS

/-- Three terminating oracle programs, with an injective signature encoding. -/
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

/-- A one-signature attacker: choose a message after seeing the public key, then forge.
Both stages may query the shared oracle and use private randomness. -/
structure Adversary (S : AlgorithmScheme P) where
  State : Type
  choose : PublicKey P → OracleComp (Spec P) (Message P × State)
  forge : State → Option S.Signature → OracleComp (Spec P) (Message P × S.Signature)

/-- The attacker wins on an accepted message-signature pair other than the signed pair.
If signing fails, any accepted pair wins. All parties share one oracle throughout. -/
def experiment (S : AlgorithmScheme P) (A : S.Adversary) : OracleComp (Spec P) Bool := do
  let (pk, sk) ← S.keygen
  let (m₁, st) ← A.choose pk
  let σ₁ ← S.sign sk m₁
  let (m₂, σ₂) ← A.forge st σ₁
  let ok ← S.verify pk m₂ σ₂
  return ok && decide (σ₁.map (fun s => (m₁, s)) ≠ some (m₂, σ₂))

/-- Strong unforgeability: success is strictly below `B / 2 ^ P.securityBits` for every
pathwise budget `B` of the whole experiment, including the honest parties' queries. -/
def Secure (S : AlgorithmScheme P) : Prop :=
  ∀ (A : S.Adversary) (B : ℕ), CostAtMost P (S.experiment A) B →
    probTrue P (S.experiment A) < (B : ℝ≥0∞) / 2 ^ P.securityBits

/-- Verification costs at most `c` on every input and every oracle-answer path, including rejects. -/
def VerifyCostAtMost (S : AlgorithmScheme P) (c : ℕ) : Prop :=
  ∀ pk m σ, CostAtMost P (S.verify pk m σ) c

/-- Key generation costs at most `b` on every oracle-answer path. -/
def KeygenCostAtMost (S : AlgorithmScheme P) (b : ℕ) : Prop := CostAtMost P S.keygen b

/-- Signing costs at most `b` for every secret key, message, and oracle-answer path. -/
def SignCostAtMost (S : AlgorithmScheme P) (b : ℕ) : Prop :=
  ∀ sk m, CostAtMost P (S.sign sk m) b

/-- Every signature in the signing program's support, for any key and message,
encodes in at most `n` bits. -/
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

/-- The probability of returning an honest signature that verification rejects is zero.
Messages may depend on the public key; signing failure is handled separately. -/
def Correct (S : AlgorithmScheme P) : Prop := ∀ message : PublicKey P → Message P,
  probTrue P (do
    let (pk, sk) ← S.keygen
    let m := message pk
    let σ ← S.sign sk m
    match σ with
    | none => return false
    | some s => return !(← S.verify pk m s)) = 0

/-- Signing failure has probability at most `ε`, averaged over honest key generation and signing,
for every public-key-dependent message choice. No adversarial oracle preprocessing is included. -/
def SigningFailureAtMost (S : AlgorithmScheme P) (ε : ℝ≥0∞) : Prop :=
  ∀ message : PublicKey P → Message P,
  probTrue P (do
    let (pk, sk) ← S.keygen
    return (← S.sign sk (message pk)).isNone) ≤ ε

/-- Generic signature-size and honest-party query-cost limits. -/
structure Limits where
  /-- Maximum encoded signature length, in bits. -/
  signatureBits : ℕ
  /-- Maximum key-generation cost, in compressions. -/
  keygenCost : ℕ
  /-- Maximum signing cost, in compressions. -/
  signCost : ℕ

/-- The paper's total signature size and honest-party budgets; no nonce format is prescribed. -/
def paperLimits : Limits where
  signatureBits := 5504
  keygenCost := 1024
  signCost := 2 ^ 20

/-- Correctness, availability, size, and cost requirements, separate from security.
The allowance `ε < 1` excludes schemes that always fail to sign. -/
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
