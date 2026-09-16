import Mathlib

/-!
# The counting factor

`countingFactor a S d` is the factor `β_a(d)` of the counting lemma, for a total weight bound `S`
and a weight threshold `d`, with `ρ = S / d`:

  `β_a(d) = ∏_{k=1}^{a} ((a - 1) ρ / (1 + ρ) + k) / (a ρ + k)`.
-/

namespace OptimalOTS

/-- The counting factor `β_a(d)` for total weight bound `S`. -/
noncomputable def countingFactor (a : ℕ) (S d : ℝ) : ℝ :=
  ∏ k ∈ Finset.range a,
    (((a : ℝ) - 1) * (S / d) / (1 + S / d) + ((k : ℝ) + 1)) / ((a : ℝ) * (S / d) + ((k : ℝ) + 1))

end OptimalOTS
