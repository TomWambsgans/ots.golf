import OptimalOTS.Statement

/-!
# One-time signatures as oracle algorithms

The model of the Generality 3/3 lower bound and of both upper bounds (compressions and RISC-V
cycles). A scheme is three oracle programs that share the random oracle of `Statement.lean` and
pay its compression costs; all other computation is free. Key generation and signing may use
private randomness; verification may not. `Admissible` collects every requirement except
security.
-/

open OracleSpec OracleComp ENNReal
noncomputable section
open scoped Classical

namespace OptimalOTS

/-- `oa` uses no private randomness: on every path, every query goes to the hash oracle. -/
def Deterministic (P : Params) {α : Type} (oa : OracleComp (Spec P) α) : Prop :=
  oa.IsQueryBound () (fun t _ => t.isRight = true) (fun _ u => u)

/-- Key generation, signing and verification as oracle programs, with an injective signature
encoding. Signing returns `none` when it fails. -/
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

/-- Strong unforgeability: the attacker wins with probability strictly below
`B / 2 ^ P.securityBits`, for every pathwise budget `B` of the whole experiment (the attacker's
queries, honest key generation and signing, and the final verification). -/
def Secure (S : AlgorithmScheme P) : Prop :=
  ∀ (A : S.Adversary) (B : ℕ), CostAtMost P (S.experiment A) B →
    probTrue P (S.experiment A) < (B : ℝ≥0∞) / 2 ^ P.securityBits

/-- Verification costs at most `c` on every input and every oracle-answer path, including rejects. -/
def VerifyCostAtMost (S : AlgorithmScheme P) (c : ℕ) : Prop :=
  ∀ pk m σ, CostAtMost P (S.verify pk m σ) c

/-- Verification uses no private randomness, on any input. -/
def VerifyDeterministic (S : AlgorithmScheme P) : Prop :=
  ∀ pk m σ, Deterministic P (S.verify pk m σ)

/-- Key generation costs at most `b` on every oracle-answer path. -/
def KeygenCostAtMost (S : AlgorithmScheme P) (b : ℕ) : Prop := CostAtMost P S.keygen b

/-- Signing costs at most `b` for every secret key, message, and oracle-answer path. -/
def SignCostAtMost (S : AlgorithmScheme P) (b : ℕ) : Prop :=
  ∀ sk m, CostAtMost P (S.sign sk m) b

/-- Every signature that signing can output encodes in at most `n` bits. -/
def SignatureSizeAtMost (S : AlgorithmScheme P) (n : ℕ) : Prop :=
  ∀ sk m σ, some σ ∈ support (S.sign sk m) → (S.encodeSignature σ).length ≤ n

/-- A signature encoding longer than `n` bits is rejected on every oracle-answer path. -/
def RejectsOversized (S : AlgorithmScheme P) (n : ℕ) : Prop :=
  ∀ pk m σ, n < (S.encodeSignature σ).length → true ∉ support (S.verify pk m σ)

/-- Perfect correctness: for every message chosen from the public key, an honest signature is
rejected with probability zero. Signing failure is bounded separately. -/
def Correct (S : AlgorithmScheme P) : Prop := ∀ message : PublicKey P → Message P,
  probTrue P (do
    let (pk, sk) ← S.keygen
    let m := message pk
    let σ ← S.sign sk m
    match σ with
    | none => return false
    | some s => return !(← S.verify pk m s)) = 0

/-- For every message chosen from the public key, signing fails with probability at most `ε`,
over honest key generation and signing. -/
def SigningFailureAtMost (S : AlgorithmScheme P) (ε : ℝ≥0∞) : Prop :=
  ∀ message : PublicKey P → Message P,
  probTrue P (do
    let (pk, sk) ← S.keygen
    return (← S.sign sk (message pk)).isNone) ≤ ε

/-- Signature size and honest-party cost limits. -/
structure Limits where
  /-- Maximum encoded signature length, in bits. -/
  signatureBits : ℕ
  /-- Maximum key-generation cost, in compressions. -/
  keygenCost : ℕ
  /-- Maximum signing cost, in compressions. -/
  signCost : ℕ

/-- The competition's limits. The signature size includes any nonce. -/
def paperLimits : Limits where
  signatureBits := 5376
  keygenCost := 1024
  signCost := 2 ^ 20

/-- Every requirement except security. `ε < 1` rules out schemes that never sign. -/
structure Admissible (S : AlgorithmScheme P) (L : Limits) (ε : ℝ≥0∞) : Prop where
  failure_lt_one : ε < 1
  correct : S.Correct
  verifyDeterministic : S.VerifyDeterministic
  signingFailure : S.SigningFailureAtMost ε
  signatureSize : S.SignatureSizeAtMost L.signatureBits
  rejectsOversized : S.RejectsOversized L.signatureBits
  keygenCost : S.KeygenCostAtMost L.keygenCost
  signCost : S.SignCostAtMost L.signCost

end AlgorithmScheme

/-- Every admissible, secure scheme needs a verification budget of at least `c`: any `v` bounding
the verification cost on every input (accepting or rejecting) satisfies `c ≤ v`. -/
def AlgorithmVerificationLowerBound (P : Params) (L : AlgorithmScheme.Limits) (ε : ℝ≥0∞)
    (c : ℕ) : Prop :=
  ∀ S : AlgorithmScheme P, S.Admissible L ε → S.Secure →
    ∀ v : ℕ, S.VerifyCostAtMost v → c ≤ v

end OptimalOTS
