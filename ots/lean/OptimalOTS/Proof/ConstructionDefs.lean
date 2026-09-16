import Mathlib

/-!
# One construction attempt

A construction attempt starts from a finite set `W` of candidate records and processes the nodes
`k` of a list in order. At each node it picks a record `ξ` uniformly from the working set, queries
the oracle table `t k` at the input `I k ξ`, and keeps exactly the records `ξ'` with
`I k ξ' = I k ξ` and `Y k ξ' = t k (I k ξ)`. It succeeds if the working set never becomes empty.

`attemptProbList I Y t ks W` is the success probability of the attempt over its private
randomness, for a fixed table `t`.
-/

open scoped Classical

namespace OptimalOTS

variable {Rec Out : Type*} {m : ℕ} {In : Fin m → Type*}

/-- Success probability of an attempt processing the nodes `ks` from working set `W`. -/
noncomputable def attemptProbList [∀ k, DecidableEq (In k)] [DecidableEq Out]
    (I : (k : Fin m) → Rec → In k) (Y : Fin m → Rec → Out)
    (t : (k : Fin m) → In k → Out) : List (Fin m) → Finset Rec → ℝ
  | [], W => if W.Nonempty then 1 else 0
  | k :: ks, W =>
    if W.Nonempty then
      (∑ ξ ∈ W, attemptProbList I Y t ks
        (W.filter fun ξ' => I k ξ' = I k ξ ∧ Y k ξ' = t k (I k ξ))) / (W.card : ℝ)
    else 0

/-- Success probability of an attempt processing all nodes `0, …, m-1` from `C`. -/
noncomputable def attemptProb [∀ k, DecidableEq (In k)] [DecidableEq Out]
    (I : (k : Fin m) → Rec → In k) (Y : Fin m → Rec → Out) (C : Finset Rec)
    (t : (k : Fin m) → In k → Out) : ℝ :=
  attemptProbList I Y t (List.finRange m) C

end OptimalOTS
