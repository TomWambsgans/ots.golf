import Submissions.RiscvUpper.CompactLevels

/-! The chain phase costs the same for every accepted index: each active chain runs its prologue
once and hashes `14 - position` times, and the positions of an accepted index sum to a constant. -/

namespace OptimalOTS.RiscvUpperProgram.Compact

open RiscvZkvm.Rv64 Forest Forest.Name RiscvUpperForest.ForestVerifier

variable (index : Idx paperParams)

theorem active_filter : (Finset.univ.filter fun k : Fin 63 => k.val < 36) = active fixedE fixedG := by
  ext k
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, fixed_active]

/-- The hash steps over the active chains: `Σ (14 - p_k) = target = 166`. -/
theorem positions_sum :
    ∑ k ∈ (Finset.univ.filter fun k : Fin 63 => k.val < 36), (14 - pos index k) = target := by
  rw [active_filter]
  exact fixedPositions_sum index

/-- The 36 prologues and 166 hash steps cost 966 cycles on every accepted index. -/
theorem costFrom_zero : costFrom index 0 = 966 := by
  rw [costFrom_eq index 63 0 rfl]
  simp only [Nat.zero_le, true_and]
  rw [← Finset.sum_filter, Finset.sum_add_distrib, Finset.sum_const, ← Finset.mul_sum,
    positions_sum, smul_eq_mul]
  have hcard : (Finset.univ.filter fun k : Fin 63 => k.val < 36).card = 36 := by decide
  rw [hcard]
  rfl

/-- The chain phase costs exactly 973 cycles on every accepted index. -/
theorem chainsCost_le : chainsCost index ≤ 973 := by
  unfold chainsCost
  rw [chainSetup_length, costFrom_zero, chainsEnd_length]

end OptimalOTS.RiscvUpperProgram.Compact
