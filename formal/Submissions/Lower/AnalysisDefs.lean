import Submissions.Lower.Attack
import Submissions.Lower.LazyEagerDefs

/-!
# Definitions for the analysis of the attack

* `Cell S`, `decode S`: the finite set of oracle cells queried in the attack experiment;
* `graphTab S g`, `nonceTab S g m`: the parts of a table used by the graph and by one message;
* `signProb`: the probability that signing returns a given index, with a nonce table;
* `bestPure`: the best rank found by the nonce search, with a nonce table;
* `attemptProbNodes`: the success probability of one construction attempt, with oracle tables;
* `succ`: the success probability of the forging step at a given rank;
* `D`: the weight of the target at a given rank.
-/

open OracleSpec OracleComp ENNReal

noncomputable section

open scoped Classical

namespace OptimalOTS

namespace Analysis

open Attack

variable {P : Params} (S : Scheme P)

/-- Inputs of message-encoding queries. -/
abbrev EncIn (P : Params) := BitVec (P.msgBits + P.nonceBits)

/-- The cells of the oracle table: one per node input, and one per message-encoding input. -/
abbrev Cell := (Σ v : Fin S.graph.size, BitVec (S.graph.kind v).inLen) ⊕ EncIn P

/-- The cell of a query, if any. -/
def decode : Query → Option (Cell S)
  | (.enc, ⟨k, u⟩) =>
    if h : k = P.msgBits + P.nonceBits then some (.inr (u.cast h)) else none
  | (.node τ, ⟨k, u⟩) =>
    if h : ∃ v, (S.graph.kind v).label? = some τ ∧ (S.graph.kind v).inLen = k then
      some (.inl ⟨Classical.choose h, u.cast (Classical.choose_spec h).2.symm⟩)
    else none

/-- The graph tables of a table on cells. -/
def graphTab (g : Cell S → BitVec P.hashBits) : S.graph.Tab := fun v u => g (.inl ⟨v, u⟩)

/-- The nonce table of message `m`. -/
def nonceTab (g : Cell S → BitVec P.hashBits) (m : Message P) : Nonce P → BitVec P.hashBits :=
  fun η => g (.inr (m ++ η))

/-- Answer hash queries through a nonce table, reading the nonce from the low bits of the input. -/
def signImpl (P : Params) (u : Nonce P → BitVec P.hashBits) : QueryImpl (Spec P) ProbComp :=
  (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)) +
    (fun q => (pure (u (q.2.2.setWidth P.nonceBits)) : ProbComp (BitVec P.hashBits)) :
      QueryImpl (hashSpec P) ProbComp)

/-- The index encoded by an oracle output. -/
def idxOfOut (P : Params) (y : BitVec P.hashBits) : ℕ := (y.setWidth P.idxBits).toNat

/-- Probability that signing `msg₁` with values `x` returns index `i`, with nonce table `u`. -/
def signProb (u : Nonce P → BitVec P.hashBits) (x : S.graph.Assignment) (i : Fin P.numSets) :
    ℝ≥0∞ :=
  ∑ η : Nonce P, if idxOfOut P (u η) = i.val then
    Pr[= some (η, S.graph.encode (S.sets i) x) | simulateQ (signImpl P u) (S.sign x (msg₁ P))]
  else 0

/-- The best rank found among the nonces `0, …, T-1` with nonce table `w` and ranking `rk`. -/
def bestPure (P : Params) (T : ℕ) (rk : ℕ → Option ℕ) (w : Nonce P → BitVec P.hashBits) :
    Option ℕ :=
  ((List.range T).filterMap fun k => rk (idxOfOut P (w (BitVec.ofNat P.nonceBits k)))).min?

/-- The candidate records of the observation of `ξ` at index `i`. -/
def obsCands (i : Fin P.numSets) (ξ : S.graph.Rec) : Finset S.graph.Rec :=
  candidates (evalHashAt S i) (reveal S i) ξ

/-- The rank of an index value if it is a valid index of rank below `100`. -/
def rkOf (i : Fin P.numSets) (C : Finset S.graph.Rec) (n : ℕ) : Option ℕ :=
  if h : n < P.numSets then
    (if rank S i C ⟨n, h⟩ < 100 then some (rank S i C ⟨n, h⟩) else none)
  else
    none

/-- The index of rank `ℓ`. -/
def rankElem (i : Fin P.numSets) (C : Finset S.graph.Rec) (ℓ : ℕ) : Fin P.numSets :=
  if h : ∃ j, rank S i C j = ℓ then Classical.choose h else i

/-- Success probability of one construction attempt over the nodes `gs` from working set `W`. -/
def attemptProbNodes (t : S.graph.Tab) : List (Fin S.graph.size) → Finset S.graph.Rec → ℝ
  | [], W => if W.Nonempty then 1 else 0
  | g :: gs, W =>
    if W.Nonempty then
      (∑ ξ ∈ W, attemptProbNodes t gs (W.filter fun ξ' =>
        (S.graph.kind g).input (S.graph.evalRec ξ') = (S.graph.kind g).input (S.graph.evalRec ξ) ∧
          ξ'.2 g = t g ((S.graph.kind g).input (S.graph.evalRec ξ)))) / (W.card : ℝ)
    else 0

/-- Success probability of the forging step at rank `ℓ`, for index `i`, sources `z` and graph
tables `t`, with `q` construction attempts. -/
def succ (q : ℕ) (i : Fin P.numSets) (ℓ : ℕ) (z : S.graph.Assignment) (t : S.graph.Tab) : ℝ :=
  let ξ := S.graph.recOf z t
  let C := obsCands S i ξ
  let j := rankElem S i C ℓ
  if j = i then 1 else 1 - (1 - attemptProbNodes S t (newNodes S i j) C) ^ q

/-- The weight of the target of rank `ℓ` for the observation of `ξ` at index `i`. -/
def D (i : Fin P.numSets) (ℓ : ℕ) (ξ : S.graph.Rec) : ℝ :=
  targetWeight S i (obsCands S i ξ) (rankElem S i (obsCands S i ξ) ℓ)

end Analysis

end OptimalOTS
