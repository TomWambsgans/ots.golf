import Submissions.RiscvUpper.CompactLevels

/-! The chain phase costs the same for every index: each chain is read once at its disclosed level
and hashed `14 - position` times, and the nibbles of an accepted index sum to `target`. -/

namespace OptimalOTS.RiscvUpperProgram.Compact

open RiscvZkvm.Rv64 Forest Forest.Name RiscvUpperForest.ForestVerifier

variable (index : Idx paperParams)

theorem srcsCost_eq : srcsCost index = ∑ k : Fin 63, srcCost index (src k) := by
  rw [srcsCost, srcs, List.map_map, Fin.sum_univ_def]
  rfl

theorem chsCost_eq (t : Fin 14) : chsCost index t = ∑ k : Fin 63, chCost index t (ch k t) := by
  rw [chsCost, chs, List.map_map, Fin.sum_univ_def]
  rfl

theorem cvsCost_eq (t : Fin 14) : cvsCost index t = ∑ k : Fin 63, cvCost index t (cv k t) := by
  rw [cvsCost, cvs, List.map_map, Fin.sum_univ_def]
  rfl

theorem levelsCost_zero : levelsCost index 0 = ∑ t : Fin 14, levelCost index t := by
  unfold levelsCost
  simp only [Nat.zero_le, if_true]

/-- One chain's cycles over the fifteen read sweeps and fourteen hash sweeps, as a function of its
disclosed position. -/
theorem perChain (p : Fin 15) :
    (if p.val = 0 then 9 else 4) +
      ∑ t : Fin 14, ((if p.val ≤ t.val then 9 else 3) + (if p.val = t.val + 1 then 9 else 4)) =
      65 + 9 * (14 - p.val) + 3 * p.val := by
  revert p
  decide

theorem active_filter : (Finset.univ.filter fun k : Fin 63 => k.val < 36) = active fixedE fixedG := by
  ext k
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, fixed_active]

theorem positions_sum :
    ∑ k ∈ (Finset.univ.filter fun k : Fin 63 => k.val < 36), (14 - pos index k) = target := by
  rw [active_filter]
  exact fixedPositions_sum index

theorem positions_total :
    ∑ k ∈ (Finset.univ.filter fun k : Fin 63 => k.val < 36), pos index k = 338 := by
  have ht : target = 166 := rfl
  have hsum : ∑ k ∈ (Finset.univ.filter fun k : Fin 63 => k.val < 36), ((14 - pos index k) + pos index k) =
      ∑ k ∈ (Finset.univ.filter fun k : Fin 63 => k.val < 36), (14 : ℕ) := by
    apply Finset.sum_congr rfl
    intro k _
    have := (fixedPositions index k).isLt
    show 14 - (fixedPositions index k).val + (fixedPositions index k).val = 14
    omega
  rw [Finset.sum_add_distrib, positions_sum, Finset.sum_const, smul_eq_mul] at hsum
  have hcard : (Finset.univ.filter fun k : Fin 63 => k.val < 36).card = 36 := by decide
  rw [hcard] at hsum
  omega

/-- The chain phase costs exactly 4854 cycles on every index. -/
theorem chainsCost_le : chainsCost index ≤ 4854 := by
  unfold chainsCost
  rw [chainSetup_length, srcsCost_eq, levelsCost_zero]
  simp only [levelCost, chsCost_eq, cvsCost_eq]
  rw [Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  have swap : ∑ t : Fin 14, ∑ k : Fin 63, (chCost index t (ch k t) + cvCost index t (cv k t)) =
      ∑ k : Fin 63, ∑ t : Fin 14, (chCost index t (ch k t) + cvCost index t (cv k t)) :=
    Finset.sum_comm
  rw [show ∑ t : Fin 14, (∑ k : Fin 63, chCost index t (ch k t) + ∑ k : Fin 63, cvCost index t (cv k t)) =
      ∑ t : Fin 14, ∑ k : Fin 63, (chCost index t (ch k t) + cvCost index t (cv k t)) by
        apply Finset.sum_congr rfl; intro t _; rw [Finset.sum_add_distrib], swap,
    ← Finset.sum_add_distrib]
  have pointwise : ∀ k : Fin 63,
      srcCost index (src k) + ∑ t : Fin 14, (chCost index t (ch k t) + cvCost index t (cv k t)) =
        if k.val < 36 then 65 + 9 * (14 - pos index k) + 3 * pos index k else 0 := by
    intro k
    by_cases hk : k.val < 36
    · rw [if_pos hk]
      have h := perChain (fixedPositions index k)
      simp only [srcCost, chCost, cvCost, readCost, hk, if_true] at *
      exact h
    · rw [if_neg hk]
      simp [srcCost, chCost, cvCost, hk]
  rw [Finset.sum_congr rfl (fun k _ => pointwise k), ← Finset.sum_filter, Finset.sum_add_distrib,
    Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, positions_sum, positions_total,
    Finset.sum_const, smul_eq_mul]
  have hcard : (Finset.univ.filter fun k : Fin 63 => k.val < 36).card = 36 := by decide
  rw [hcard]
  norm_num [target]

end OptimalOTS.RiscvUpperProgram.Compact
