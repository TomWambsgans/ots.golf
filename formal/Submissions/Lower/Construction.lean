import Submissions.Lower.Entropy
import Submissions.Lower.ConstructionDefs

/-!
# The construction bound

A record `ξ` is chosen uniformly from the candidate set `C`, and an oracle table `t` uniformly
among the tables consistent with it: `t k (I k ξ) = Y k ξ` for every node `k`. The expected value
of `-log₂` of the attempt's success probability is at most
`∑ₖ (log₂ |Out| - H(Y k | trace before k, I k))`.
-/

open scoped Classical

namespace OptimalOTS

variable {Rec Out : Type*} {m : ℕ} {In : Fin m → Type*}

noncomputable def attemptWeight [∀ k, DecidableEq (In k)] [DecidableEq Out]
    (I : (k : Fin m) → Rec → In k) (Y : Fin m → Rec → Out) :
    List (Fin m) → Finset Rec → Rec → ℝ
  | [], _, _ => 1
  | k :: L, W, ξ =>
    ((W.filter fun ξ' => I k ξ' = I k ξ).card : ℝ) /
      ((W.filter fun ξ' => I k ξ' = I k ξ ∧ Y k ξ' = Y k ξ).card : ℝ) *
      attemptWeight I Y L (W.filter fun ξ' => I k ξ' = I k ξ ∧ Y k ξ' = Y k ξ) ξ

theorem attemptProbList_eq [∀ k, DecidableEq (In k)] [DecidableEq Out]
    (I : (k : Fin m) → Rec → In k) (Y : Fin m → Rec → Out)
    (t : (k : Fin m) → In k → Out) (L : List (Fin m)) (W : Finset Rec) :
    attemptProbList I Y t L W =
      (∑ ξ ∈ W.filter (fun ξ => ∀ k ∈ L, t k (I k ξ) = Y k ξ), attemptWeight I Y L W ξ) /
        (W.card : ℝ) := by
  induction L generalizing W with
  | nil =>
    rcases W.eq_empty_or_nonempty with rfl | hW
    · simp [attemptProbList]
    · simp [attemptProbList, attemptWeight, hW, Finset.card_pos.mpr hW |>.ne']
  | cons k L ih =>
    rcases W.eq_empty_or_nonempty with rfl | hW
    · simp [attemptProbList]
    simp only [attemptProbList, if_pos hW]
    congr 1
    -- LHS rewrite
    have h1 : ∀ ξ' ∈ W, attemptProbList I Y t L
        (W.filter fun ξ'' => I k ξ'' = I k ξ' ∧ Y k ξ'' = t k (I k ξ')) =
        ∑ ξ ∈ W, if (I k ξ' = I k ξ ∧ (t k (I k ξ) = Y k ξ ∧ ∀ j ∈ L, t j (I j ξ) = Y j ξ))
          then attemptWeight I Y L (W.filter fun ξ'' => I k ξ'' = I k ξ ∧ Y k ξ'' = Y k ξ) ξ /
            ((W.filter fun ξ'' => I k ξ'' = I k ξ ∧ Y k ξ'' = Y k ξ).card : ℝ) else 0 := by
      intro ξ' _
      rw [ih, Finset.sum_div, Finset.filter_filter, Finset.sum_filter]
      refine Finset.sum_congr rfl fun ξ _ => ?_
      by_cases hc : I k ξ' = I k ξ ∧ (t k (I k ξ) = Y k ξ ∧ ∀ j ∈ L, t j (I j ξ) = Y j ξ)
      · have hset : (W.filter fun ξ'' => I k ξ'' = I k ξ' ∧ Y k ξ'' = t k (I k ξ')) =
            (W.filter fun ξ'' => I k ξ'' = I k ξ ∧ Y k ξ'' = Y k ξ) := by
          apply Finset.filter_congr
          intro x _
          rw [hc.1, hc.2.1]
        have hc' : (I k ξ = I k ξ' ∧ Y k ξ = t k (I k ξ')) ∧ ∀ j ∈ L, t j (I j ξ) = Y j ξ :=
          ⟨⟨hc.1.symm, by rw [hc.1]; exact hc.2.1.symm⟩, hc.2.2⟩
        rw [if_pos hc', if_pos hc, hset]
      · have hc' : ¬ ((I k ξ = I k ξ' ∧ Y k ξ = t k (I k ξ')) ∧ ∀ j ∈ L, t j (I j ξ) = Y j ξ) := by
          rintro ⟨⟨h1, h2⟩, h3⟩
          exact hc ⟨h1.symm, by rw [h2, h1], h3⟩
        rw [if_neg hc', if_neg hc]
    rw [Finset.sum_congr rfl h1, Finset.sum_comm, Finset.sum_filter]
    refine Finset.sum_congr rfl fun ξ _ => ?_
    simp only [List.forall_mem_cons]
    by_cases hc : t k (I k ξ) = Y k ξ ∧ ∀ j ∈ L, t j (I j ξ) = Y j ξ
    · simp only [and_iff_left hc]
      rw [if_pos hc, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, attemptWeight]
      ring
    · simp [hc]


/-- The input-output pairs of `ξ` at the nodes before `k`, with the others hidden. -/
def traceBefore (I : (k : Fin m) → Rec → In k) (Y : Fin m → Rec → Out) (k : Fin m) (ξ : Rec) :
    (j : Fin m) → Option (In j × Out) :=
  fun j => if j < k then some (I j ξ, Y j ξ) else none

theorem traceBefore_eq_iff (I : (k : Fin m) → Rec → In k) (Y : Fin m → Rec → Out) (k : Fin m)
    (ξ ξ' : Rec) : traceBefore I Y k ξ' = traceBefore I Y k ξ ↔
      ∀ i : Fin m, i.val < k.val → I i ξ' = I i ξ ∧ Y i ξ' = Y i ξ := by
  rw [funext_iff]
  refine forall_congr' fun i => ?_
  by_cases h : i < k
  · have h' : i.val < k.val := h
    simp [traceBefore, h, h']
  · have h' : ¬ i.val < k.val := h
    simp [traceBefore, h, h']

noncomputable def traceRatio [∀ k, DecidableEq (In k)] [DecidableEq Out]
    (I : (k : Fin m) → Rec → In k) (Y : Fin m → Rec → Out) (C : Finset Rec) (k : Fin m) (ξ : Rec) :
    ℝ :=
  ((C.filter fun ω' => (traceBefore I Y k ω', I k ω') = (traceBefore I Y k ξ, I k ξ)).card : ℝ) /
    ((C.filter fun ω' => Y k ω' = Y k ξ ∧
      (traceBefore I Y k ω', I k ω') = (traceBefore I Y k ξ, I k ξ)).card : ℝ)

theorem agreeUpTo_succ_iff (I : (k : Fin m) → Rec → In k) (Y : Fin m → Rec → Out) (ξ x : Rec)
    (j : ℕ) (hj : j < m) :
    (∀ i : Fin m, i.val < j + 1 → I i x = I i ξ ∧ Y i x = Y i ξ) ↔
      (∀ i : Fin m, i.val < j → I i x = I i ξ ∧ Y i x = Y i ξ) ∧
        (I ⟨j, hj⟩ x = I ⟨j, hj⟩ ξ ∧ Y ⟨j, hj⟩ x = Y ⟨j, hj⟩ ξ) := by
  constructor
  · intro h
    exact ⟨fun i hi => h i (by omega), h ⟨j, hj⟩ (by simp)⟩
  · rintro ⟨h1, h2⟩ i hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | hi
    · exact h1 i hi
    · have : i = ⟨j, hj⟩ := Fin.ext hi
      subst this
      exact h2

theorem attemptWeight_drop [∀ k, DecidableEq (In k)] [DecidableEq Out]
    (I : (k : Fin m) → Rec → In k) (Y : Fin m → Rec → Out) (C : Finset Rec) (ξ : Rec) :
    ∀ n j, j + n = m →
      attemptWeight I Y ((List.finRange m).drop j)
        (C.filter fun ξ' => ∀ i : Fin m, i.val < j → I i ξ' = I i ξ ∧ Y i ξ' = Y i ξ) ξ =
      ∏ k ∈ Finset.univ.filter (fun k : Fin m => j ≤ k.val), traceRatio I Y C k ξ := by
  intro n
  induction n with
  | zero =>
    intro j hj
    rw [List.drop_eq_nil_of_le (by simp; omega), attemptWeight, Finset.filter_false_of_mem, Finset.prod_empty]
    intro k _
    have := k.isLt
    omega
  | succ n ih =>
    intro j hjn
    have hj : j < m := by omega
    rw [List.drop_eq_getElem_cons (by simpa using hj), List.getElem_finRange, attemptWeight,
      Finset.filter_filter, Finset.filter_filter]
    have hW : (C.filter fun ξ' => (∀ i : Fin m, i.val < j → I i ξ' = I i ξ ∧ Y i ξ' = Y i ξ) ∧
        (I ⟨j, hj⟩ ξ' = I ⟨j, hj⟩ ξ ∧ Y ⟨j, hj⟩ ξ' = Y ⟨j, hj⟩ ξ)) =
        C.filter fun ξ' => ∀ i : Fin m, i.val < j + 1 → I i ξ' = I i ξ ∧ Y i ξ' = Y i ξ := by
      apply Finset.filter_congr
      intro x _
      exact (agreeUpTo_succ_iff I Y ξ x j hj).symm
    simp only [Fin.cast_mk]
    rw [hW, ih (j + 1) (by omega)]
    have hprod : Finset.univ.filter (fun k : Fin m => j ≤ k.val) =
        insert ⟨j, hj⟩ (Finset.univ.filter (fun k : Fin m => j + 1 ≤ k.val)) := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
      omega
    rw [hprod, Finset.prod_insert (by simp)]
    congr 1
    unfold traceRatio
    congr 2
    · congr 1
      apply Finset.filter_congr
      intro x _
      rw [Prod.mk.injEq, traceBefore_eq_iff]
    · congr 1
      apply Finset.filter_congr
      intro x _
      rw [Prod.mk.injEq, traceBefore_eq_iff, agreeUpTo_succ_iff I Y ξ x j hj]
      tauto

theorem attemptWeight_finRange [∀ k, DecidableEq (In k)] [DecidableEq Out]
    (I : (k : Fin m) → Rec → In k) (Y : Fin m → Rec → Out) (C : Finset Rec) (ξ : Rec) :
    attemptWeight I Y (List.finRange m) C ξ = ∏ k, traceRatio I Y C k ξ := by
  have h := attemptWeight_drop I Y C ξ m 0 (by omega)
  rw [List.drop_zero, Finset.filter_true_of_mem (fun _ _ i hi => absurd hi (by omega)),
    Finset.filter_true_of_mem (fun _ _ => by omega)] at h
  exact h

theorem traceRatio_pos [∀ k, DecidableEq (In k)] [DecidableEq Out]
    (I : (k : Fin m) → Rec → In k) (Y : Fin m → Rec → Out) (C : Finset Rec) (k : Fin m) {ξ : Rec}
    (hξ : ξ ∈ C) : 0 < traceRatio I Y C k ξ := by
  unfold traceRatio
  apply div_pos <;> exact_mod_cast Finset.card_pos.mpr ⟨ξ, by simp [hξ]⟩

theorem condEntropy_eq_sum_traceRatio [∀ k, DecidableEq (In k)] [DecidableEq Out]
    (I : (k : Fin m) → Rec → In k) (Y : Fin m → Rec → Out) (C : Finset Rec) (k : Fin m) :
    condEntropy C (Y k) (fun ξ => (traceBefore I Y k ξ, I k ξ)) =
      ∑ ω ∈ C, (1 / (C.card : ℝ)) * Real.logb 2 (traceRatio I Y C k ω) := by
  unfold condEntropy traceRatio
  convert rfl

theorem card_tables_consistent [Fintype Out] [DecidableEq Out] [∀ k, Fintype (In k)] [∀ k, DecidableEq (In k)]
    (u : (k : Fin m) → In k) (y : Fin m → Out) :
    Fintype.card Out ^ m *
      (Finset.univ.filter fun t : ((k : Fin m) → In k → Out) => ∀ k, t k (u k) = y k).card =
      Fintype.card ((k : Fin m) → In k → Out) := by
  have h1 : (Finset.univ.filter fun t : ((k : Fin m) → In k → Out) => ∀ k, t k (u k) = y k) =
      Fintype.piFinset fun k => Finset.univ.filter (fun f : In k → Out => f (u k) = y k) := by
    ext t
    simp [Fintype.mem_piFinset]
  rw [h1, Fintype.card_piFinset, Fintype.card_pi]
  have h2 : ∀ k, Fintype.card Out * (Finset.univ.filter fun f : In k → Out => f (u k) = y k).card =
      Fintype.card (In k → Out) := by
    intro k
    have := Fintype.card_filter_piFinset_eq_of_mem (fun _ : In k => (Finset.univ : Finset Out))
      (u k) (a := y k) (Finset.mem_univ _)
    rw [Fintype.piFinset_univ] at this
    rw [this, Fintype.card_fun, Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ, Finset.card_univ, ← pow_succ']
    congr
    have := Fintype.card_pos (α := In k) (h := ⟨u k⟩)
    omega
  rw [← Finset.prod_congr rfl (fun k _ => h2 k), Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]

/-- The construction bound (inequality (log-success) in Lemma 3 of the paper). -/
theorem sum_neg_logb_attemptProb_le [Fintype Rec] [Fintype Out] [Nonempty Out] [DecidableEq Out]
    [∀ k, Fintype (In k)] [∀ k, DecidableEq (In k)]
    (I : (k : Fin m) → Rec → In k) (Y : Fin m → Rec → Out) (C : Finset Rec) (hC : C.Nonempty) :
    let P : Finset (Rec × ((k : Fin m) → In k → Out)) :=
      (C ×ˢ Finset.univ).filter fun p => ∀ k, p.2 k (I k p.1) = Y k p.1
    (∑ p ∈ P, -Real.logb 2 (attemptProb I Y C p.2)) / (P.card : ℝ) ≤
      ∑ k : Fin m, (Real.logb 2 (Fintype.card Out) -
        condEntropy C (Y k) (fun ξ => (traceBefore I Y k ξ, I k ξ))) := by
  intro P
  have hK : 0 < Fintype.card Out := Fintype.card_pos
  have hKR : (0 : ℝ) < (Fintype.card Out : ℝ) := by exact_mod_cast hK
  have hN : 0 < C.card := Finset.card_pos.mpr hC
  have hNR : (0 : ℝ) < (C.card : ℝ) := by exact_mod_cast hN
  obtain ⟨ξ0, hξ0⟩ := hC
  set c := (Finset.univ.filter fun t : ((k : Fin m) → In k → Out) =>
    ∀ k, t k (I k ξ0) = Y k ξ0).card with hc_def
  have hcard : ∀ ξ, (Finset.univ.filter fun t : ((k : Fin m) → In k → Out) =>
      ∀ k, t k (I k ξ) = Y k ξ).card = c := by
    intro ξ
    have h1 := card_tables_consistent (fun k => I k ξ) (fun k => Y k ξ)
    have h2 := card_tables_consistent (fun k => I k ξ0) (fun k => Y k ξ0)
    exact Nat.eq_of_mul_eq_mul_left (pow_pos hK m) (h1.trans h2.symm)
  have hcpos : 0 < c := by
    have h2 := card_tables_consistent (fun k => I k ξ0) (fun k => Y k ξ0)
    have : 0 < Fintype.card ((k : Fin m) → In k → Out) := Fintype.card_pos
    rw [← h2] at this
    exact Nat.pos_of_mul_pos_left this
  have hcR : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hcpos
  have hsumP : ∀ g : Rec × ((k : Fin m) → In k → Out) → ℝ, ∑ q ∈ P, g q =
      ∑ ξ ∈ C, ∑ t ∈ (Finset.univ.filter fun t : ((k : Fin m) → In k → Out) =>
        ∀ k, t k (I k ξ) = Y k ξ), g (ξ, t) := by
    intro g
    simp only [P]
    rw [Finset.sum_filter, Finset.sum_product]
    refine Finset.sum_congr rfl fun ξ _ => ?_
    rw [Finset.sum_filter]
  have hsumP' : ∀ g : Rec × ((k : Fin m) → In k → Out) → ℝ, ∑ q ∈ P, g q =
      ∑ t : ((k : Fin m) → In k → Out),
        ∑ ξ ∈ C.filter (fun ξ => ∀ k, t k (I k ξ) = Y k ξ), g (ξ, t) := by
    intro g
    simp only [P]
    rw [Finset.sum_filter, Finset.sum_product_right]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Finset.sum_filter]
  have hPcard : (P.card : ℝ) = C.card * c := by
    rw [Finset.card_eq_sum_ones, Nat.cast_sum, hsumP]
    simp only [Nat.cast_one, Finset.sum_const, nsmul_eq_mul, mul_one, hcard]
  have hT : (Fintype.card ((k : Fin m) → In k → Out) : ℝ) = (Fintype.card Out : ℝ) ^ m * c := by
    exact_mod_cast (card_tables_consistent (fun k => I k ξ0) (fun k => Y k ξ0)).symm
  set R : Rec → ℝ := fun ξ => attemptWeight I Y (List.finRange m) C ξ with hR_def
  have hp : ∀ t, attemptProb I Y C t =
      (∑ ξ ∈ C.filter (fun ξ => ∀ k, t k (I k ξ) = Y k ξ), R ξ) / (C.card : ℝ) := by
    intro t
    unfold attemptProb
    rw [attemptProbList_eq]
    congr 2
    apply Finset.filter_congr
    simp
  have hR : ∀ ξ ∈ C, 0 < R ξ := by
    intro ξ hξ
    simp only [hR_def, attemptWeight_finRange]
    exact Finset.prod_pos fun k _ => traceRatio_pos I Y C k hξ
  have hlogR : ∀ ξ ∈ C, Real.log (R ξ) = ∑ k, Real.log (traceRatio I Y C k ξ) := by
    intro ξ hξ
    simp only [hR_def, attemptWeight_finRange]
    exact Real.log_prod fun k _ => (traceRatio_pos I Y C k hξ).ne'
  have hppos : ∀ q ∈ P, 0 < attemptProb I Y C q.2 := by
    intro q hq
    simp only [P, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true] at hq
    rw [hp]
    refine div_pos ?_ hNR
    exact Finset.sum_pos' (fun ξ hξ => (hR ξ (Finset.mem_filter.1 hξ).1).le)
      ⟨q.1, Finset.mem_filter.2 ⟨hq.1, hq.2⟩, hR _ hq.1⟩
  have hRP : ∀ q ∈ P, 0 < R q.1 := by
    intro q hq
    simp only [P, Finset.mem_filter, Finset.mem_product] at hq
    exact hR _ hq.1.1
  have hx : ∑ q ∈ P, R q.1 / ((Fintype.card Out : ℝ) ^ m * attemptProb I Y C q.2) ≤
      (P.card : ℝ) := by
    rw [hsumP']
    calc _ = ∑ t : ((k : Fin m) → In k → Out),
          (∑ ξ ∈ C.filter (fun ξ => ∀ k, t k (I k ξ) = Y k ξ), R ξ) /
            ((Fintype.card Out : ℝ) ^ m * attemptProb I Y C t) := by
          simp_rw [Finset.sum_div]
      _ ≤ ∑ t : ((k : Fin m) → In k → Out), (C.card : ℝ) / (Fintype.card Out : ℝ) ^ m := by
          refine Finset.sum_le_sum fun t _ => ?_
          by_cases h : attemptProb I Y C t = 0
          · rw [h, mul_zero, div_zero]
            positivity
          · have h' := hp t
            rw [eq_div_iff hNR.ne'] at h'
            rw [← h']
            field_simp
            rfl
      _ = (P.card : ℝ) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hT, hPcard]
          field_simp
  have hpt : ∀ q ∈ P, -Real.log (attemptProb I Y C q.2) ≤
      (R q.1 / ((Fintype.card Out : ℝ) ^ m * attemptProb I Y C q.2) - 1) - Real.log (R q.1) +
        m * Real.log (Fintype.card Out) := by
    intro q hq
    have hpq := hppos q hq
    have hRq := hRP q hq
    have h1 := Real.log_le_sub_one_of_pos
      (x := R q.1 / ((Fintype.card Out : ℝ) ^ m * attemptProb I Y C q.2)) (by positivity)
    rw [Real.log_div hRq.ne' (by positivity), Real.log_mul (by positivity) hpq.ne',
      Real.log_pow] at h1
    linarith
  have hsumR : ∑ q ∈ P, Real.log (R q.1) =
      c * ∑ k, ∑ ξ ∈ C, Real.log (traceRatio I Y C k ξ) := by
    rw [hsumP, Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ξ hξ => ?_
    show ∑ t ∈ _, Real.log (R ξ) = _
    rw [Finset.sum_const, hcard, nsmul_eq_mul, hlogR ξ hξ]
  have key : ∑ q ∈ P, -Real.log (attemptProb I Y C q.2) ≤
      C.card * c * (m * Real.log (Fintype.card Out)) -
        c * ∑ k, ∑ ξ ∈ C, Real.log (traceRatio I Y C k ξ) := by
    calc _ ≤ ∑ q ∈ P, ((R q.1 / ((Fintype.card Out : ℝ) ^ m * attemptProb I Y C q.2) - 1) -
          Real.log (R q.1) + m * Real.log (Fintype.card Out)) := Finset.sum_le_sum hpt
      _ = (∑ q ∈ P, R q.1 / ((Fintype.card Out : ℝ) ^ m * attemptProb I Y C q.2) - P.card) -
          ∑ q ∈ P, Real.log (R q.1) + P.card * (m * Real.log (Fintype.card Out)) := by
          rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
            Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul, mul_one]
      _ ≤ _ := by
          rw [hsumR, ← hPcard]
          linarith
  have hRHS : ∑ k : Fin m, (Real.logb 2 (Fintype.card Out) -
      condEntropy C (Y k) (fun ξ => (traceBefore I Y k ξ, I k ξ))) =
      (m * Real.log (Fintype.card Out) -
        (∑ k, ∑ ξ ∈ C, Real.log (traceRatio I Y C k ξ)) / C.card) / Real.log 2 := by
    simp only [condEntropy_eq_sum_traceRatio, ← Real.log_div_log]
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    simp_rw [← Finset.mul_sum, ← Finset.sum_div]
    field_simp
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  rw [hRHS, div_le_iff₀ (by rw [hPcard]; positivity)]
  simp only [← Real.log_div_log, ← neg_div, ← Finset.sum_div]
  calc _ ≤ (C.card * c * (m * Real.log (Fintype.card Out)) -
        c * ∑ k, ∑ ξ ∈ C, Real.log (traceRatio I Y C k ξ)) / Real.log 2 :=
        div_le_div_of_nonneg_right key hlog2.le
    _ = _ := by
        rw [hPcard]
        field_simp

end OptimalOTS
