import Submissions.Lower.CountingFactor

/-!
# Definitions for the numerical bounds

The explicit inequalities of Appendix B of the paper, for the parameters
`S_* = 5257`, `a = 21`, `M = 2^115`, `K = 500` (counting), `K' = 450` (ranks searched),
`d₀ = 113`, `q = 2^110`, `T = 5 · 2^120`, `N = 2^128`, and an index query of cost `2`.
-/

namespace OptimalOTS.Numerics

/-- The number of construction attempts. -/
def q : ℕ := 2 ^ 110

/-- The number of nonce trials. -/
def T : ℕ := 5 * 2 ^ 120

/-- The number of possible index values. -/
def N : ℕ := 2 ^ 128

/-- Probability that the nonce search finds rank `ℓ` as its best rank (`1 ≤ ℓ`). -/
noncomputable def omega (ℓ : ℕ) : ℝ :=
  (1 - ((ℓ : ℝ) - 1) / N) ^ T - (1 - (ℓ : ℝ) / N) ^ T

/-- Lower bound on the average construction success at rank `ℓ` (`1 ≤ ℓ ≤ 450`). -/
noncomputable def rankSuccess (ℓ : ℕ) : ℝ :=
  if ℓ = 1 then 1 else
    let z : ℝ := 512 * ((ℓ : ℝ) - 1) / 255500
    511 / 512 * (1 - 21 / 20 * z ^ ((1 : ℝ) / 21) + z / 20)

/-- Probability that signing fails. -/
noncomputable def signFailure : ℝ := (1 - (2 : ℝ)⁻¹ ^ 13) ^ (2 ^ 21)

/-- The total cost of the attack. -/
def attackCost : ℕ := 1024 + 2 ^ 21 * 2 + T * 2 + (q + 2) * 22 + 2 * 2

end OptimalOTS.Numerics
