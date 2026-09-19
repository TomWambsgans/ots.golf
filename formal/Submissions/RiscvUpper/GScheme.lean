import Submissions.RiscvUpper.Valid

/-!
# Graph schemes with an accepted-index predicate

The paper scheme of `OptimalOTS.Statement` accepts an index when it is below `numSets`. The
scheme of this root accepts an index when it lies in `validSet P` (its 32 nibbles are at most 14
and sum to `target`), so that the machine reads the chain positions directly from the index.
Everything else (graph, key generation, signing loop, verification, strong-forgery experiment)
is the paper's definition verbatim.
-/

open OracleSpec OracleComp ENNReal

noncomputable section

open scoped Classical

namespace OptimalOTS

/-- A graph-based one-time signature scheme whose disclosure sets are indexed by the accepted
indices. -/
structure GScheme (P : Params) where
  /-- The public computation. -/
  graph : Graph P
  /-- The disclosure sets. -/
  sets : Idx P → Finset (Fin graph.size)
  /-- The verifier must recompute the root. -/
  root_not_mem : ∀ i, graph.root ∉ sets i
  /-- The revealed values suffice: `sets i` meets every path from a secret source to the root. -/
  no_hidden_source :
    ∀ i v, graph.Visited (sets i) v → v ∉ sets i → ¬ (graph.kind v).IsSource
  /-- Signatures reveal at most `maxRevealBits` bits besides the nonce. -/
  reveal_le : ∀ i, graph.revealBits (sets i) ≤ P.maxRevealBits
  /-- Key generation costs at most `keygenBudget`. -/
  keygen_le : graph.keygenCost ≤ P.keygenBudget

namespace GScheme

variable {P : Params} (S : GScheme P)

/-- Resize the root value to `pkBits`: truncation keeps the low bits; extension pads with zeros. -/
def publicKey (x : S.graph.Assignment) : PublicKey P := (x S.graph.root).setWidth P.pkBits

/-- Key generation; the secret key is the value of every node. -/
def keygen : OracleComp (Spec P) (PublicKey P × S.graph.Assignment) := do
  let x ← S.graph.keygen
  return (S.publicKey x, x)

/-- Signing with at most `k` further trials, never retrying a nonce in `tried`. -/
def signLoop (x : S.graph.Assignment) (m : Message P) :
    ℕ → Finset (Nonce P) → OracleComp (Spec P) (Option (Signature P))
  | 0, _ => pure none
  | k + 1, tried =>
    let fresh := Finset.univ \ tried
    if h : 0 < fresh.card then do
      let j ← (liftM ($[0..(fresh.card - 1)]) : OracleComp (Spec P) (Fin (fresh.card - 1 + 1)))
      let η : Nonce P := (fresh.equivFin.symm (Fin.cast (by omega) j)).1
      let i ← index P m η
      if hi : i ∈ validSet P then
        return some (η, S.graph.encode (S.sets ⟨i, hi⟩) x)
      else
        signLoop x m k (insert η tried)
    else
      pure none

/-- Try at most `trialLimit` distinct uniform nonces; return `none` if none selects a valid index. -/
def sign (x : S.graph.Assignment) (m : Message P) : OracleComp (Spec P) (Option (Signature P)) :=
  S.signLoop x m P.trialLimit ∅

/-- Reject invalid indices or payload lengths; otherwise reconstruct the root and compare its
public-key bits with `pk`. -/
def verify (pk : PublicKey P) (m : Message P) (σ : Signature P) : OracleComp (Spec P) Bool := do
  let i ← index P m σ.1
  if hi : i ∈ validSet P then
    let A := S.sets ⟨i, hi⟩
    if σ.2.length = S.graph.revealBits A then
      let y ← S.graph.reconstruct A (S.graph.decode A σ.2)
      return decide (S.publicKey y = pk)
    else
      return false
  else
    return false

/-- Verification cost at a valid index and payload length: the index query plus reconstruction. -/
def verifyCost (i : Idx P) : ℕ := idxCost P + S.graph.reconstructCost (S.sets i)

/-- Strong-forgery experiment. The attacker wins when its pair is accepted and differs from the
signed pair; after signing failure, any accepted pair wins. All parties share one oracle table. -/
def experiment (A : Adversary P) : OracleComp (Spec P) Bool := do
  let (pk, sk) ← S.keygen
  let (m₁, st) ← A.choose pk
  let σ₁ ← S.sign sk m₁
  let (m₂, σ₂) ← A.forge st σ₁
  let ok ← S.verify pk m₂ σ₂
  return ok && decide (σ₁.map (fun s => (m₁, s)) ≠ some (m₂, σ₂))

/-- Strong unforgeability: for every attacker and pathwise budget `B` for the entire experiment,
the probability of an accepted fresh pair is strictly below `B / 2 ^ securityBits`. -/
def Secure : Prop :=
  ∀ (A : Adversary P) (B : ℕ), CostAtMost P (S.experiment A) B →
    probTrue P (S.experiment A) < (B : ℝ≥0∞) / 2 ^ P.securityBits

end GScheme

end OptimalOTS
