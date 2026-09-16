import Mathlib

/-!
# Conditional entropy for a uniform choice from a finite set

`condEntropy C U V` is the conditional Shannon entropy, in bits, of `U` given `V` when `ω` is
chosen uniformly from the finite set `C`:

  `H(U | V) = E_ω [ log₂ (#{ω' ∈ C : V ω' = V ω} / #{ω' ∈ C : U ω' = U ω ∧ V ω' = V ω}) ]`.

An unconditional entropy is obtained with a constant `V`.
-/

open scoped Classical

namespace OptimalOTS

/-- Conditional entropy (in bits) of `U` given `V` for `ω` uniform on `C`. -/
noncomputable def condEntropy {Ω α β : Type*} (C : Finset Ω) (U : Ω → α) (V : Ω → β) : ℝ :=
  ∑ ω ∈ C, (1 / (C.card : ℝ)) *
    Real.logb 2 (((C.filter fun ω' => V ω' = V ω).card : ℝ) /
      ((C.filter fun ω' => U ω' = U ω ∧ V ω' = V ω).card : ℝ))

end OptimalOTS
