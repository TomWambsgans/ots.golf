import Submissions.Lower.Semantics
import Submissions.Lower.Information

/-!
# The attack

The attacker of the paper, for a scheme `S`, `q` construction attempts and `T` nonce trials:

1. request a signature on `msg₁`;
2. recompute its index `i`, reconstruct the root from the revealed values, and form the candidate
   records consistent with everything observed;
3. compute the weights and rank all disclosure indices by the weight of the hash nodes they would
   newly evaluate (index `i` first);
4. try `T` nonces for `msg₂` and keep the best-ranked index among the 450 lowest ranks;
5. reuse the received values if that index is `i`, and otherwise run up to `q` construction
   attempts and output the values of a surviving candidate.
-/

open OracleSpec OracleComp ENNReal

noncomputable section

open scoped Classical

namespace OptimalOTS

namespace Attack

variable {P : Params} (S : Scheme P)

/-- The message whose signature is requested. -/
def msg₁ (P : Params) : Message P := 0

/-- The message of the forgery. -/
def msg₂ (P : Params) : Message P := 1

/-- The hash nodes evaluated when verifying at index `i`. -/
def evalHashAt (i : Fin P.numSets) : Finset (Fin S.graph.size) :=
  S.graph.evalHash (S.sets i)

/-- The values revealed at index `i` by the record `ξ`. -/
def reveal (i : Fin P.numSets) (ξ : S.graph.Rec) : (v : S.sets i) → BitVec (S.graph.len v) :=
  fun v => S.graph.evalRec ξ v

/-- The candidate records for received values `xa` and reconstructed values `xr` at index `i`. -/
def cands (i : Fin P.numSets) (xa xr : S.graph.Assignment) : Finset S.graph.Rec :=
  Finset.univ.filter fun ξ =>
    (∀ v ∈ S.sets i, S.graph.evalRec ξ v = xa v) ∧
      ∀ g ∈ evalHashAt S i, ξ.2 g = (S.graph.kind g).output (xr g)

/-- The weight of node `g` for candidate set `C` at index `i`. -/
def weight (i : Fin P.numSets) (C : Finset S.graph.Rec) (g : Fin S.graph.size) : ℝ :=
  if g ∈ evalHashAt S i then 0 else
    Real.logb 2 (Fintype.card (BitVec P.hashBits)) -
      condEntropy C (fun ξ => ξ.2 g) (fun ξ => (ξ.1, outputsBefore ξ.2 g))

/-- The hash nodes other than the root evaluated when verifying at index `j`. -/
def targetSet (j : Fin P.numSets) : Finset (Fin S.graph.size) :=
  (evalHashAt S j).erase S.graph.root

/-- The weight of target index `j`. -/
def targetWeight (i : Fin P.numSets) (C : Finset S.graph.Rec) (j : Fin P.numSets) : ℝ :=
  ∑ g ∈ targetSet S j, weight S i C g

/-- Sort key of target `j`: its weight, then `i` before the others, then the index. -/
def key (i : Fin P.numSets) (C : Finset S.graph.Rec) (j : Fin P.numSets) : Lex (ℝ × Lex (ℕ × ℕ)) :=
  toLex (targetWeight S i C j, toLex (if j = i then 0 else 1, j.val))

/-- Rank of target `j` (starting at `0`). -/
def rank (i : Fin P.numSets) (C : Finset S.graph.Rec) (j : Fin P.numSets) : ℕ :=
  (Finset.univ.filter fun j' => key S i C j' < key S i C j).card

/-- One nonce trial: keep the best rank below `450` found so far, with its index and nonce. -/
def searchStep (i : Fin P.numSets) (C : Finset S.graph.Rec)
    (best : Option (ℕ × Fin P.numSets × Nonce P)) (k : ℕ) :
    OracleComp (Spec P) (Option (ℕ × Fin P.numSets × Nonce P)) := do
  let η : Nonce P := BitVec.ofNat P.nonceBits k
  let j ← index P (msg₂ P) η
  if hj : j < P.numSets then
    let r := rank S i C ⟨j, hj⟩
    if r < 450 ∧ ∀ b ∈ best, r < b.1 then
      return some (r, ⟨j, hj⟩, η)
    else
      return best
  else
    return best

/-- The nonce search over the nonces `0, …, T-1`. -/
def search (T : ℕ) (i : Fin P.numSets) (C : Finset S.graph.Rec) :
    OracleComp (Spec P) (Option (ℕ × Fin P.numSets × Nonce P)) :=
  (List.range T).foldlM (searchStep S i C) none

/-- One construction attempt over the nodes `gs` from the working set `C`. -/
def attemptM : Finset S.graph.Rec → List (Fin S.graph.size) →
    OracleComp (Spec P) (Option S.graph.Rec)
  | C, [] => pure (if h : C.Nonempty then some (Classical.choose h) else none)
  | C, g :: gs =>
    if h : 0 < C.card then do
      let k ← (liftM ($[0..(C.card - 1)]) : OracleComp (Spec P) (Fin (C.card - 1 + 1)))
      let ξ := (C.equivFin.symm (Fin.cast (by omega) k)).1
      let u := (S.graph.kind g).input (S.graph.evalRec ξ)
      let a ← (S.graph.kind g).query P u
      attemptM
        (C.filter fun ξ' => (S.graph.kind g).input (S.graph.evalRec ξ') = u ∧ ξ'.2 g = a) gs
    else
      pure none

/-- Up to `n` construction attempts; returns the first surviving record. -/
def attempts (C : Finset S.graph.Rec) (gs : List (Fin S.graph.size)) :
    ℕ → OracleComp (Spec P) (Option S.graph.Rec)
  | 0 => pure none
  | n + 1 => do
    match (← attemptM S C gs) with
    | some ξ => pure (some ξ)
    | none => attempts C gs n

/-- The hash nodes evaluated at `j` but not at `i`, in node order. -/
def newNodes (i j : Fin P.numSets) : List (Fin S.graph.size) :=
  (List.finRange S.graph.size).filter fun g => decide (g ∈ evalHashAt S j ∧ g ∉ evalHashAt S i)

/-- The output when the attack gives up. -/
def giveUp (P : Params) : Message P × Signature P := (msg₂ P, (0, []))

/-- The forging stage. -/
def forge (q T : ℕ) : Option (Signature P) → OracleComp (Spec P) (Message P × Signature P)
  | none => pure (giveUp P)
  | some (η₁, pl) => do
    let i ← index P (msg₁ P) η₁
    if hi : i < P.numSets then
      let i' : Fin P.numSets := ⟨i, hi⟩
      let xa := S.graph.decode (S.sets i') pl
      let xr ← S.graph.reconstruct (S.sets i') xa
      let C := cands S i' xa xr
      match (← search S T i' C) with
      | none => pure (giveUp P)
      | some (_, j, η₂) =>
        if j = i' then
          pure (msg₂ P, (η₂, pl))
        else
          match (← attempts S C (newNodes S i' j) q) with
          | none => pure (giveUp P)
          | some ξ' => pure (msg₂ P, (η₂, S.graph.encode (S.sets j) (S.graph.evalRec ξ')))
    else
      pure (giveUp P)

/-- The attacker. -/
def adversary (q T : ℕ) : Adversary P where
  State := Unit
  choose _ := pure (msg₁ P, ())
  forge _ σ := forge S q T σ

end Attack

end OptimalOTS
