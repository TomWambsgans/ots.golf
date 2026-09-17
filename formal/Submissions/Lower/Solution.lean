import OptimalOTS.Statement
import Submissions.Lower.Cost
import Submissions.Lower.Assembly

/-!
# The main theorem

`verificationLowerBound_paper` proves the statement `VerificationLowerBound paperParams 25` of
`OptimalOTS.Statement`: with the parameters of the paper, every secure graph-based one-time
signature scheme has a signature whose verification costs at least 25 compressions.

The proof assumes the contrary, builds the attack of `Submissions.Lower.Attack`, bounds its total
cost (`Attack.costAtMost_experiment`) and its success probability (`Assembly.probTrue_gt`), and
contradicts the security requirement.
-/

open OracleSpec OracleComp ENNReal

noncomputable section

open scoped Classical

namespace OptimalOTS


/-- **Main theorem.** For the parameters of the paper, every secure graph-based one-time
signature scheme has a signature whose verification costs at least 25 compressions. -/
theorem verificationLowerBound_paper : VerificationLowerBound paperParams 25 := by
  intro S hS
  by_contra hcon
  push Not at hcon
  have hcost : ∀ i, S.verifyCost i ≤ 24 := fun i => Nat.lt_succ_iff.mp (hcon i)
  have hidx : idxCost paperParams = 2 := by decide
  have hB := Attack.costAtMost_experiment S Numerics.q Numerics.T 22 fun i => by
    have := hcost i
    simp only [Scheme.verifyCost, hidx] at this
    omega
  have hsec := hS _ _ hB
  have hprob := Assembly.probTrue_gt S hcost
  have hcostval : ((paperParams.keygenBudget + paperParams.trialLimit * idxCost paperParams +
      Numerics.T * idxCost paperParams + (Numerics.q + 2) * 22 + 2 * idxCost paperParams : ℕ) :
        ℝ≥0∞) / 2 ^ paperParams.securityBits < ENNReal.ofReal (3 / 32) := by
    have hval : (paperParams.keygenBudget + paperParams.trialLimit * idxCost paperParams +
        Numerics.T * idxCost paperParams + (Numerics.q + 2) * 22 + 2 * idxCost paperParams : ℕ) =
        Numerics.attackCost := by rw [hidx]; rfl
    rw [hval, ← ENNReal.ofReal_natCast, show (2 : ℝ≥0∞) ^ paperParams.securityBits =
        ENNReal.ofReal ((2 : ℝ) ^ 127) by
          rw [ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]; rfl,
      ← ENNReal.ofReal_div_of_pos (by norm_num)]
    rw [ENNReal.ofReal_lt_ofReal_iff (by norm_num)]
    linarith [Numerics.attackCost_div_lt]
  exact absurd (hprob.trans hsec) (not_lt.mpr hcostval.le)

/-- **Exported certificate of the lower track.** Its statement must be exactly the one in
`OptimalOTS/Challenge/Lower.lean.in` with the number of `claim.txt` substituted. -/
theorem Challenge.Lower.candidate : VerificationLowerBound paperParams 25 :=
  verificationLowerBound_paper

end OptimalOTS
