import OptimalOTS.Statement
import OptimalOTS.Proof.Cost
import OptimalOTS.Proof.Assembly

/-!
# The main theorem

`verificationLowerBound_paper` proves the statement `VerificationLowerBound paperParams 25` of
`OptimalOTS.Statement`: with the parameters of the paper, every secure graph-based one-time
signature scheme has a signature whose verification costs at least 25 hash units.

The proof assumes the contrary, builds the attack of `OptimalOTS.Proof.Attack`, bounds its total
cost (`Attack.costAtMost_experiment`) and its success probability (`Assembly.probTrue_gt`), and
contradicts the security requirement.
-/

open OracleSpec OracleComp ENNReal

noncomputable section

open scoped Classical

namespace OptimalOTS


/-- **Main theorem.** For the parameters of the paper, every secure graph-based one-time
signature scheme has a signature whose verification costs at least 25 hash units. -/
theorem verificationLowerBound_paper : VerificationLowerBound paperParams 25 := by
  intro S hS
  by_contra hcon
  push Not at hcon
  have hcost : ∀ i, S.verifyCost i ≤ 24 := fun i => Nat.lt_succ_iff.mp (hcon i)
  have hB := Attack.costAtMost_experiment S Numerics.q Numerics.T 23 (by decide) fun i => by
    have := hcost i
    simp only [Scheme.verifyCost] at this
    omega
  have hsec := hS _ _ hB
  have hprob := Assembly.probTrue_gt S hcost
  have hcostval : ((paperParams.keygenBudget + paperParams.trialLimit + Numerics.T +
      (Numerics.q + 2) * 23 + 2 : ℕ) : ℝ≥0∞) / 2 ^ paperParams.securityBits <
      ENNReal.ofReal (11 / 200) := by
    have hval : (paperParams.keygenBudget + paperParams.trialLimit + Numerics.T +
        (Numerics.q + 2) * 23 + 2 : ℕ) = Numerics.attackCost := rfl
    rw [hval, ← ENNReal.ofReal_natCast, show (2 : ℝ≥0∞) ^ paperParams.securityBits =
        ENNReal.ofReal ((2 : ℝ) ^ 127) by
          rw [ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]; rfl,
      ← ENNReal.ofReal_div_of_pos (by norm_num)]
    rw [ENNReal.ofReal_lt_ofReal_iff (by norm_num)]
    linarith [Numerics.attackCost_div_lt]
  exact absurd (hprob.trans hsec) (not_lt.mpr hcostval.le)

end OptimalOTS
