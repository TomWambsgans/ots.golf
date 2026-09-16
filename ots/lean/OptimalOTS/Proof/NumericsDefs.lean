import OptimalOTS.Proof.CountingFactor

/-!
# Definitions for the numerical bounds

The explicit inequalities of Appendix B of the paper, for the parameters
`S_* = 5257`, `a = 22`, `M = 2^115`, `q = 5 · 2^113`, `T = 3 · 2^121`, `N = 2^128`.
-/

namespace OptimalOTS.Numerics

/-- The number of construction attempts. -/
def q : ℕ := 5 * 2 ^ 113

/-- The number of nonce trials. -/
def T : ℕ := 3 * 2 ^ 121

/-- The number of possible index values. -/
def N : ℕ := 2 ^ 128

/-- Probability that the nonce search finds rank `ℓ` as its best rank (`1 ≤ ℓ`). -/
noncomputable def omega (ℓ : ℕ) : ℝ :=
  (1 - ((ℓ : ℝ) - 1) / N) ^ T - (1 - (ℓ : ℝ) / N) ^ T

/-- Lower bound on the average construction success at rank `ℓ` (`1 ≤ ℓ ≤ 100`). -/
noncomputable def rankSuccess (ℓ : ℕ) : ℝ :=
  if ℓ = 1 then 1 else
    let z : ℝ := 512 * ((ℓ : ℝ) - 1) / 51100
    511 / 512 * (1 - 22 / 21 * z ^ ((1 : ℝ) / 22) + z / 21)

/-- Probability that signing fails. -/
noncomputable def signFailure : ℝ := (1 - (2 : ℝ)⁻¹ ^ 13) ^ (2 ^ 21)

/-- The total cost of the attack. -/
def attackCost : ℕ := 1024 + 2 ^ 21 + T + (q + 2) * 23 + 2

end OptimalOTS.Numerics
