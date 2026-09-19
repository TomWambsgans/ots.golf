import OptimalOTS.Dag

/-! Internal numeric checks, not part of the contract. The DAG signing format fills the signing
and size budgets, and `numCuts = 2 ^ 115` is the smallest power of two for which `trials`
failed trials have probability at most `1 / 2 ^ signingFailureBits`. -/

namespace OptimalOTS.Witnesses

-- `norm_num` evaluates `(1 - 2 ^ -13) ^ 2 ^ 13` exactly.
set_option exponentiation.threshold 20000

open OptimalOTS.Dag

/-- An index query costs one compression, so the signer may try `2 ^ 20` nonces; the nonce
leaves 5376 bits of revealed values. -/
example : idxCost = 1 ∧ trials = 2 ^ 20 ∧ trials * idxCost = signBudget ∧
    maxSignatureBits - nonceBits = 5376 := by decide

/-- A trial finds a valid index with probability `2 ^ -13`. -/
example : numCuts * 2 ^ 13 = 2 ^ idxBits := by decide

/-- With `numCuts` cuts, all trials fail with probability at most `2 ^ -128`. -/
theorem signingFailure_le :
    (1 - (numCuts : ℚ) / 2 ^ idxBits) ^ trials ≤ 1 / 2 ^ signingFailureBits := by
  have hq : (1 - (numCuts : ℚ) / 2 ^ idxBits) = 1 - 1 / 2 ^ 13 := by
    norm_num [numCuts, idxBits]
  have ht : trials = 2 ^ 13 * 2 ^ 7 := by decide
  have key : (1 - 1 / 2 ^ 13 : ℚ) ^ 2 ^ 13 ≤ 1 / 2 := by norm_num
  rw [hq, ht, pow_mul, signingFailureBits]
  calc ((1 - 1 / 2 ^ 13 : ℚ) ^ 2 ^ 13) ^ 2 ^ 7 ≤ (1 / 2) ^ 2 ^ 7 :=
        pow_le_pow_left₀ (by norm_num) key _
    _ = 1 / 2 ^ 128 := by norm_num

/-- With half as many cuts, all trials would fail with probability above `2 ^ -128`. -/
theorem signingFailure_half_gt :
    1 / 2 ^ signingFailureBits < (1 - ((numCuts / 2 : ℕ) : ℚ) / 2 ^ idxBits) ^ trials := by
  have hq : (1 - ((numCuts / 2 : ℕ) : ℚ) / 2 ^ idxBits) = 1 - 1 / 2 ^ 14 := by
    norm_num [numCuts, idxBits]
  have ht : trials = 2 ^ 14 * 2 ^ 6 := by decide
  have key : (1 / 4 : ℚ) < (1 - 1 / 2 ^ 14) ^ 2 ^ 14 := by norm_num
  rw [hq, ht, pow_mul, signingFailureBits]
  calc (1 / 2 ^ 128 : ℚ) = (1 / 4) ^ 2 ^ 6 := by norm_num
    _ < ((1 - 1 / 2 ^ 14 : ℚ) ^ 2 ^ 14) ^ 2 ^ 6 :=
        pow_lt_pow_left₀ key (by norm_num) (by norm_num)

end OptimalOTS.Witnesses

/--
info: 'OptimalOTS.Witnesses.signingFailure_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms OptimalOTS.Witnesses.signingFailure_le

/--
info: 'OptimalOTS.Witnesses.signingFailure_half_gt' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms OptimalOTS.Witnesses.signingFailure_half_gt
