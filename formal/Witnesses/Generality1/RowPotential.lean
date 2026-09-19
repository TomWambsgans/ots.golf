import Witnesses.Generality1.Rows
import Witnesses.Generality1.RowIneq

/-!
# The row potential

`psi d = r + Σ_m max (b_m − r a_m) 0 / D_m` (see `docs/nonce-128-analysis.md`, section 2): `r` is
the fraction of accepted indices held by the cache, and row `m` has `a_m` accepted entries, `b_m` of
them shared, and `D_m = a_m + q N_m` with `N_m` its uncached nonces and `q = numSets / 2^idxBits`.

* `psi_step`: one fresh encoding answer raises `psi` by at most the class bound `gCls` of its index;
* `sum_gCls_le`: the class bounds add up to at most `11/6` over all indices;
* `psi_charge`: hence `θ psi` grows by at most `2 / 2^idxBits` on average, `θ = I / (I − 2L)`;
* `psi_dom`: `θ psi` is a valid `ρ` for the signing lemma `signRho_bound`.
-/

open OracleSpec OracleComp ENNReal

noncomputable section

open scoped Classical

namespace OptimalOTS

/-- The standing hypotheses on the parameters. -/
structure RowHyp (P : Params) (F : DagFormat) : Prop where
  nonce_eq : F.nonceBits = F.idxBits
  idx_le : F.idxBits ≤ P.hashBits
  two_le : 2 ≤ F.numSets
  numSets_le : 2 * F.numSets ≤ 2 ^ F.idxBits
  trial_le : 24 * F.trialLimit ≤ 2 ^ F.idxBits

variable (P : Params) (F : DagFormat)

namespace Row

def I : ℝ := 2 ^ F.idxBits
def M : ℝ := F.numSets
def q : ℝ := M F / I F
def θ : ℝ := I F / (I F - 2 * F.trialLimit)

variable (d : Cache P) (m : Message P)

def v : ℝ := (V P F d).card
def r : ℝ := v P F d / M F
def a : ℝ := (rowAcc P F d m).card
def b : ℝ := (rowBad P F d m).card
def dd : ℝ := (rowAcc P F d m \ rowBad P F d m).card
def u : ℝ := (rowCached P F d m).card
def N : ℝ := 2 ^ F.nonceBits - u P F d m
def D : ℝ := a P F d m + q F * N P F d m
def x : ℝ := b P F d m - r P F d * a P F d m
def pr : ℝ := max (x P F d m) 0 / D P F d m
def hit (i : ℕ) : ℝ := (rowHit P F d m i).card

end Row

/-- The row potential. -/
def psi (d : Cache P) : ℝ := Row.r P F d + ∑ m, Row.pr P F d m

/-- The bound on the growth of `psi` when the answer to `m₀ ++ η₀` has index `i`. -/
def gCls (d : Cache P) (m₀ : Message P) (i : ℕ) : ℝ :=
  if F.numSets ≤ i then
    max (Row.x P F d m₀) 0 / (Row.D P F d m₀ - Row.q F) - max (Row.x P F d m₀) 0 / Row.D P F d m₀
  else if i ∈ V P F d then (1 - Row.r P F d) / Row.D P F d m₀ + ∑ m, Row.hit P F d m i / Row.D P F d m
  else 1 / Row.M F

namespace Row

/-! ## Real inequalities -/

theorem step_real (x x' D D' t : ℝ) (hD : 0 < D) (hDD : D ≤ D') (ht : 0 ≤ t)
    (hx : x' ≤ x + t) : max x' 0 / D' ≤ max x 0 / D + t / D := by
  have h1 : max x' 0 ≤ max x 0 + t :=
    max_le (by linarith [le_max_left x 0]) (by linarith [le_max_right x 0])
  have h2 : 0 ≤ max x 0 + t := add_nonneg (le_max_right _ _) ht
  calc max x' 0 / D' ≤ (max x 0 + t) / D' := div_le_div_of_nonneg_right h1 (by linarith)
    _ ≤ (max x 0 + t) / D := div_le_div_of_nonneg_left h2 hD hDD
    _ = _ := add_div _ _ _

theorem rej_real (x x' D q : ℝ) (hDq : 0 < D - q) (hx : x' ≤ x) :
    max x' 0 / (D - q) ≤ max x 0 / D + (max x 0 / (D - q) - max x 0 / D) := by
  rw [add_sub_cancel]
  exact div_le_div_of_nonneg_right (max_le_max hx le_rfl) hDq.le

theorem budget_real (d t D M : ℝ) (hM : 0 < M) (hd : 0 ≤ d) (ht0 : 0 ≤ t) (htM : t ≤ M)
    (hD : d + M - t ≤ D) : d / D ≤ (d + t) / M := by
  rcases hd.eq_or_lt with h | h
  · rw [← h, zero_div, zero_add]
    exact div_nonneg ht0 hM.le
  have hpos : 0 < d + M - t := by linarith
  calc d / D ≤ d / (d + M - t) := div_le_div_of_nonneg_left hd hpos hD
    _ ≤ (d + t) / M := by
      rw [div_le_div_iff₀ hpos hM]
      nlinarith [sq_nonneg d, mul_nonneg ht0 (sub_nonneg.2 htM)]

/-! ## Basic facts -/

variable {P F}

theorem I_pos : 0 < I F := by unfold I; positivity

theorem M_pos (hP : RowHyp P F) : 0 < M F := by
  unfold M; have := hP.two_le; exact_mod_cast (by omega : 0 < F.numSets)

theorem two_le_M (hP : RowHyp P F) : 2 ≤ M F := by
  unfold M; exact_mod_cast hP.two_le

theorem two_M_le (hP : RowHyp P F) : 2 * M F ≤ I F := by
  unfold M I; exact_mod_cast hP.numSets_le

theorem q_nonneg : 0 ≤ q F := by
  unfold q M; exact div_nonneg (Nat.cast_nonneg _) I_pos.le

theorem q_le_half (hP : RowHyp P F) : q F ≤ 1 / 2 := by
  unfold q
  rw [div_le_iff₀ I_pos]
  linarith [two_M_le hP]

theorem qI : q F * I F = M F := div_mul_cancel₀ _ I_pos.ne'

theorem nonce_card (hP : RowHyp P F) : (2 : ℝ) ^ F.nonceBits = I F := by
  rw [hP.nonce_eq]; rfl

theorem u_nonneg (d : Cache P) (m : Message P) : 0 ≤ u P F d m := Nat.cast_nonneg _

theorem u_le_card (d : Cache P) (m : Message P) : u P F d m ≤ 2 ^ F.nonceBits := by
  unfold u
  have : (rowCached P F d m).card ≤ 2 ^ F.nonceBits := by
    calc (rowCached P F d m).card ≤ (Finset.univ : Finset (Nonce F)).card :=
          Finset.card_le_card (Finset.subset_univ _)
      _ = 2 ^ F.nonceBits := by rw [Finset.card_univ, Fintype.card_bitVec]
  exact_mod_cast this

theorem N_nonneg (d : Cache P) (m : Message P) : 0 ≤ N P F d m := by
  unfold N; linarith [u_le_card (F := F) d m]

theorem a_nonneg (d : Cache P) (m : Message P) : 0 ≤ a P F d m := Nat.cast_nonneg _
theorem dd_nonneg (d : Cache P) (m : Message P) : 0 ≤ dd P F d m := Nat.cast_nonneg _
theorem v_nonneg (d : Cache P) : 0 ≤ v P F d := Nat.cast_nonneg _
theorem hit_nonneg (d : Cache P) (m : Message P) (i : ℕ) : 0 ≤ hit P F d m i := Nat.cast_nonneg _

theorem b_le_a (d : Cache P) (m : Message P) : b P F d m ≤ a P F d m := by
  unfold a b; exact_mod_cast Finset.card_le_card (rowBad_subset P F d m)

theorem dd_le_a (d : Cache P) (m : Message P) : dd P F d m ≤ a P F d m := by
  unfold a dd; exact_mod_cast Finset.card_le_card Finset.sdiff_subset

theorem v_le_M (d : Cache P) : v P F d ≤ M F := by
  unfold v M; exact_mod_cast card_V_le_numSets P F d

theorem r_nonneg (hP : RowHyp P F) (d : Cache P) : 0 ≤ r P F d :=
  div_nonneg (v_nonneg d) (M_pos hP).le

theorem r_le_one (hP : RowHyp P F) (d : Cache P) : r P F d ≤ 1 := by
  unfold r; rw [div_le_one (M_pos hP)]; exact v_le_M d

theorem rM (hP : RowHyp P F) (d : Cache P) : r P F d * M F = v P F d :=
  div_mul_cancel₀ _ (M_pos hP).ne'

theorem D_nonneg (d : Cache P) (m : Message P) : 0 ≤ D P F d m :=
  add_nonneg (a_nonneg d m) (mul_nonneg q_nonneg (N_nonneg d m))

theorem pr_nonneg (d : Cache P) (m : Message P) : 0 ≤ pr P F d m :=
  div_nonneg (le_max_right _ _) (D_nonneg d m)

section Budget

variable (hP : RowHyp P F) {d : Cache P} (hc : 2 * encCount P F d ≤ 2 ^ F.idxBits)
include hP hc

theorem sum_u_le : ∑ m, u P F d m ≤ I F / 2 := by
  have h1 : (∑ m, (rowCached P F d m).card : ℕ) ≤ encCount P F d := sum_rowCached_le P F d
  have h2 : ((2 * encCount P F d : ℕ) : ℝ) ≤ ((2 ^ F.idxBits : ℕ) : ℝ) := by exact_mod_cast hc
  push_cast at h2
  unfold u I
  have h3 : (∑ m, ((rowCached P F d m).card : ℝ)) ≤ encCount P F d := by exact_mod_cast h1
  linarith

theorem u_le_half (m : Message P) : u P F d m ≤ I F / 2 :=
  (Finset.single_le_sum (fun m _ => u_nonneg d m) (Finset.mem_univ m)).trans (sum_u_le hP hc)

theorem N_ge (m : Message P) : I F / 2 ≤ N P F d m := by
  unfold N; rw [nonce_card hP]; linarith [u_le_half hP hc m]

theorem N_le (m : Message P) : N P F d m ≤ I F := by
  unfold N; rw [nonce_card hP]; linarith [u_nonneg (F := F) d m]

theorem qN_ge (m : Message P) : M F / 2 ≤ q F * N P F d m := by
  have := mul_le_mul_of_nonneg_left (N_ge hP hc m) (q_nonneg (F := F))
  rw [← qI (F := F)]; linarith

theorem qN_le (m : Message P) : q F * N P F d m ≤ M F := by
  have := mul_le_mul_of_nonneg_left (N_le hP hc m) (q_nonneg (F := F))
  rw [← qI (F := F)]; linarith

theorem D_ge (m : Message P) : M F / 2 ≤ D P F d m := by
  unfold D; linarith [a_nonneg (F := F) d m, qN_ge hP hc m]

theorem D_pos (m : Message P) : 0 < D P F d m := by
  linarith [D_ge hP hc m, M_pos hP]

theorem one_le_D (m : Message P) : 1 ≤ D P F d m := by
  linarith [D_ge hP hc m, two_le_M hP]

end Budget

end Row

theorem psi_nonneg (hP : RowHyp P F) (d : Cache P) : 0 ≤ psi P F d :=
  add_nonneg (Row.r_nonneg hP d) (Finset.sum_nonneg fun m _ => Row.pr_nonneg d m)

theorem psi_empty : psi P F ∅ = 0 := by
  have hV : V P F ∅ = ∅ := by
    ext i; simp [mem_V_iff]
  have hA : ∀ m, rowAcc P F ∅ m = ∅ := fun m => by ext; simp [rowAcc]
  have hB : ∀ m, rowBad P F ∅ m = ∅ := fun m => by ext; simp [rowBad]
  simp [psi, Row.r, Row.v, Row.pr, Row.x, Row.a, Row.b, hV, hA, hB]

theorem psi_of_ne {d : Cache P} {q : Query} (hq : ∀ u : EncInput P F, q ≠ encQuery P F u)
    (w : BitVec P.hashBits) : psi P F (d.cacheQuery q w) = psi P F d := by
  simp only [psi, Row.r, Row.v, Row.pr, Row.x, Row.a, Row.b, Row.D, Row.N, Row.u,
    V_of_ne hq, rowAcc_of_ne hq, rowBad_of_ne hq, rowCached_of_ne hq]

/-! ## One fresh encoding answer -/

section Step

variable {P F} (hP : RowHyp P F) {d : Cache P} (hc : 2 * encCount P F d ≤ 2 ^ F.idxBits)
  {m₀ : Message P} {η₀ : Nonce F} (hfresh : d (encQuery P F (m₀ ++ η₀)) = none)
  (w : BitVec P.hashBits)
include hP hc hfresh

theorem psi_step :
    psi P F (d.cacheQuery (encQuery P F (m₀ ++ η₀)) w) ≤ psi P F d + gCls P F d m₀ (idxOf P F w) := by
  set d' := d.cacheQuery (encQuery P F (m₀ ++ η₀)) w with hd'
  set i := idxOf P F w with hi
  have hu : ∀ m, Row.u P F d' m = Row.u P F d m + if m = m₀ then 1 else 0 := fun m => by
    simp only [Row.u, hd', rowCached_cacheQuery w hfresh m]; push_cast; rfl
  have ha : ∀ m, Row.a P F d' m = Row.a P F d m + if m = m₀ ∧ i < F.numSets then 1 else 0 :=
    fun m => by simp only [Row.a, hd', rowAcc_cacheQuery w hfresh m]; push_cast; rfl
  have hv : Row.v P F d' = Row.v P F d + if i < F.numSets ∧ i ∉ V P F d then 1 else 0 := by
    simp only [Row.v, hd', V_cacheQuery w hfresh]; push_cast; rfl
  have hb : ∀ m, Row.b P F d' m ≤
      Row.b P F d m + Row.hit P F d m i + if m = m₀ ∧ i ∈ V P F d then 1 else 0 := fun m => by
    have := rowBad_cacheQuery w hfresh m
    simp only [Row.b, Row.hit, hd']
    exact_mod_cast this
  have hD : ∀ m, Row.D P F d' m = Row.D P F d m + (if m = m₀ ∧ i < F.numSets then 1 else 0) -
      Row.q F * (if m = m₀ then 1 else 0) := fun m => by
    simp only [Row.D, Row.N, ha, hu]; ring
  have hDpos : ∀ m, 0 < Row.D P F d m := fun m => Row.D_pos hP hc m
  have hq1 : Row.q F ≤ 1 := by linarith [Row.q_le_half hP]
  have hr0 := Row.r_nonneg hP d
  unfold psi gCls
  split_ifs with h1 h2
  · -- a rejected index
    have hnV : i ∉ V P F d := fun h => absurd (V_lt_numSets P F d i h) (by omega)
    have hr : Row.r P F d' = Row.r P F d := by
      simp only [Row.r, hv, if_neg (fun h : i < F.numSets ∧ i ∉ V P F d => by omega), add_zero]
    have hrow : ∀ m, Row.pr P F d' m ≤ Row.pr P F d m + if m = m₀ then
        (max (Row.x P F d m₀) 0 / (Row.D P F d m₀ - Row.q F) - max (Row.x P F d m₀) 0 / Row.D P F d m₀)
        else 0 := fun m => by
      have hbm := hb m
      have hhit : Row.hit P F d m i = 0 := by simp [Row.hit, rowHit_eq_empty P F d m hnV]
      have hx : Row.x P F d' m ≤ Row.x P F d m := by
        simp only [Row.x, hr, ha m, if_neg (fun h : m = m₀ ∧ i < F.numSets => by omega),
          add_zero]
        simp only [hhit, if_neg (fun h : m = m₀ ∧ i ∈ V P F d => hnV h.2), add_zero] at hbm
        linarith
      by_cases hm : m = m₀
      · rw [if_pos hm]
        subst hm
        have hD' : Row.D P F d' m = Row.D P F d m - Row.q F := by
          rw [hD m]; simp [show ¬ i < F.numSets by omega]
        unfold Row.pr
        rw [hD']
        exact Row.rej_real _ _ _ _ (by linarith [Row.one_le_D hP hc m, Row.q_le_half hP]) hx
      · rw [if_neg hm, add_zero]
        have hD' : Row.D P F d' m = Row.D P F d m := by rw [hD m]; simp [hm]
        unfold Row.pr
        rw [hD']
        exact div_le_div_of_nonneg_right (max_le_max hx le_rfl) (hDpos m).le
    calc Row.r P F d' + ∑ m, Row.pr P F d' m
        ≤ Row.r P F d + ∑ m, (Row.pr P F d m + if m = m₀ then
          (max (Row.x P F d m₀) 0 / (Row.D P F d m₀ - Row.q F) -
            max (Row.x P F d m₀) 0 / Row.D P F d m₀) else 0) := by
          rw [hr]; exact add_le_add le_rfl (Finset.sum_le_sum fun m _ => hrow m)
      _ = _ := by
          rw [Finset.sum_add_distrib, Finset.sum_ite_eq']
          simp only [Finset.mem_univ, if_true]
          ring
  · -- an index already held
    have hlt : i < F.numSets := by omega
    have hr : Row.r P F d' = Row.r P F d := by
      simp only [Row.r, hv, if_neg (fun h : i < F.numSets ∧ i ∉ V P F d => h.2 h2), add_zero]
    have hrow : ∀ m, Row.pr P F d' m ≤ Row.pr P F d m + Row.hit P F d m i / Row.D P F d m +
        if m = m₀ then (1 - Row.r P F d) / Row.D P F d m else 0 := fun m => by
      have hbm := hb m
      have hDD : Row.D P F d m ≤ Row.D P F d' m := by
        rw [hD m]; by_cases hm : m = m₀ <;> simp [hm, hlt] <;> linarith
      have hr1 := Row.r_le_one hP d
      have hh0 := Row.hit_nonneg (F := F) d m i
      by_cases hm : m = m₀
      · rw [if_pos hm]
        have ham : Row.a P F d' m = Row.a P F d m + 1 := by
          rw [ha m, if_pos ⟨hm, hlt⟩]
        have hbm' : Row.b P F d' m ≤ Row.b P F d m + Row.hit P F d m i + 1 := by
          rw [if_pos ⟨hm, h2⟩] at hbm; exact hbm
        have hx : Row.x P F d' m ≤ Row.x P F d m + (Row.hit P F d m i + (1 - Row.r P F d)) := by
          simp only [Row.x]
          rw [ham, hr]
          linarith
        have := Row.step_real _ _ _ _ _ (hDpos m) hDD (by linarith) hx
        unfold Row.pr
        rw [add_div] at this
        linarith
      · rw [if_neg hm]
        have hx : Row.x P F d' m ≤ Row.x P F d m + Row.hit P F d m i := by
          simp only [Row.x, hr, ha m, hm, false_and, if_false, add_zero]
          simp only [hm, false_and, if_false, add_zero] at hbm
          linarith
        have := Row.step_real _ _ _ _ _ (hDpos m) hDD hh0 hx
        unfold Row.pr
        linarith
    calc Row.r P F d' + ∑ m, Row.pr P F d' m
        ≤ Row.r P F d + ∑ m, (Row.pr P F d m + Row.hit P F d m i / Row.D P F d m +
          if m = m₀ then (1 - Row.r P F d) / Row.D P F d m else 0) := by
          rw [hr]; exact add_le_add le_rfl (Finset.sum_le_sum fun m _ => hrow m)
      _ = _ := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq']
          simp only [Finset.mem_univ, if_true]
          ring
  · -- a new accepted index
    have hlt : i < F.numSets := by omega
    have hnV : i ∉ V P F d := h2
    have hM := Row.M_pos hP
    have hr : Row.r P F d' = Row.r P F d + 1 / Row.M F := by
      simp only [Row.r, hv, if_pos (⟨hlt, hnV⟩ : i < F.numSets ∧ i ∉ V P F d)]
      ring
    have hrow : ∀ m, Row.pr P F d' m ≤ Row.pr P F d m := fun m => by
      have hbm := hb m
      have hhit : Row.hit P F d m i = 0 := by simp [Row.hit, rowHit_eq_empty P F d m hnV]
      simp only [hhit, if_neg (fun h : m = m₀ ∧ i ∈ V P F d => hnV h.2), add_zero] at hbm
      have hDD : Row.D P F d m ≤ Row.D P F d' m := by
        rw [hD m]; by_cases hm : m = m₀ <;> simp [hm, hlt] <;> linarith
      have ha' : Row.a P F d m ≤ Row.a P F d' m := by
        rw [ha m]; split_ifs <;> linarith
      have hr' : Row.r P F d ≤ Row.r P F d' := by
        rw [hr]; linarith [one_div_pos.2 hM]
      have hx : Row.x P F d' m ≤ Row.x P F d m + 0 := by
        simp only [Row.x]
        nlinarith [Row.a_nonneg (F := F) d m]
      have := Row.step_real _ _ _ _ _ (hDpos m) hDD le_rfl hx
      unfold Row.pr
      linarith [zero_div (Row.D P F d m)]
    calc Row.r P F d' + ∑ m, Row.pr P F d' m ≤ Row.r P F d + 1 / Row.M F + ∑ m, Row.pr P F d m := by
          rw [hr]; exact add_le_add le_rfl (Finset.sum_le_sum fun m _ => hrow m)
      _ = _ := by ring

end Step

/-! ## Summing the class bounds -/

section Classes

variable {P F} (hP : RowHyp P F) {d : Cache P} (hc : 2 * encCount P F d ≤ 2 ^ F.idxBits)
include hP hc

theorem sum_gCls_le (m₀ : Message P) :
    ∑ i ∈ Finset.range (2 ^ F.idxBits), gCls P F d m₀ i ≤ 11 / 6 := by
  have hM := Row.M_pos hP
  have hMI2 := Row.two_M_le hP
  have hMIn : F.numSets ≤ 2 ^ F.idxBits := by have := hP.numSets_le; omega
  have hVsub : V P F d ⊆ Finset.range F.numSets := fun i hi =>
    Finset.mem_range.2 (V_lt_numSets P F d i hi)
  set A := max (Row.x P F d m₀) 0 / (Row.D P F d m₀ - Row.q F) -
    max (Row.x P F d m₀) 0 / Row.D P F d m₀ with hA
  set B := (1 - Row.r P F d) / Row.D P F d m₀ with hB
  have hF1 : (Finset.range (2 ^ F.idxBits)).filter (fun i => F.numSets ≤ i) =
      Finset.Ico F.numSets (2 ^ F.idxBits) := by
    ext i; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega
  have hF2 : ((Finset.range (2 ^ F.idxBits)).filter (fun i => ¬ F.numSets ≤ i)).filter
      (fun i => i ∈ V P F d) = V P F d := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · exact fun h => h.2
    · intro h
      have := V_lt_numSets P F d i h
      exact ⟨⟨by omega, by omega⟩, h⟩
  have hF3 : ((Finset.range (2 ^ F.idxBits)).filter (fun i => ¬ F.numSets ≤ i)).filter
      (fun i => i ∉ V P F d) = Finset.range F.numSets \ V P F d := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_sdiff]
    constructor
    · rintro ⟨⟨-, h⟩, h'⟩; exact ⟨by omega, h'⟩
    · rintro ⟨h, h'⟩; exact ⟨⟨by omega, by omega⟩, h'⟩
  have hdd : ∀ m, Row.dd P F d m = ∑ i ∈ V P F d, Row.hit P F d m i := fun m => by
    simp only [Row.dd, Row.hit]
    rw [← sum_rowHit]
    push_cast
    rfl
  have e1 : ∑ _i ∈ Finset.Ico F.numSets (2 ^ F.idxBits), A = (Row.I F - Row.M F) * A := by
    rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, Nat.cast_sub hMIn]
    simp [Row.I, Row.M]
  have e2 : ∑ i ∈ V P F d, (B + ∑ m, Row.hit P F d m i / Row.D P F d m) =
      Row.v P F d * B + ∑ m, Row.dd P F d m / Row.D P F d m := by
    rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, Finset.sum_comm]
    congr 1
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [← Finset.sum_div, hdd]
  have e3 : ∑ _i ∈ Finset.range F.numSets \ V P F d, 1 / Row.M F = 1 - Row.r P F d := by
    rw [Finset.sum_const, Finset.card_sdiff_of_subset hVsub, Finset.card_range, nsmul_eq_mul,
      Nat.cast_sub (card_V_le_numSets P F d)]
    simp only [Row.r, Row.v, Row.M]
    have : (F.numSets : ℝ) ≠ 0 := hM.ne'
    field_simp
  have hsum : ∑ i ∈ Finset.range (2 ^ F.idxBits), gCls P F d m₀ i =
      (Row.I F - Row.M F) * A + (Row.v P F d * B + ∑ m, Row.dd P F d m / Row.D P F d m) +
        (1 - Row.r P F d) := by
    unfold gCls
    rw [Finset.sum_ite, Finset.sum_ite, hF1, hF2, hF3, e1, e2, e3]
    ring
  rw [hsum, ← Finset.add_sum_erase _ _ (Finset.mem_univ m₀)]
  set S := ∑ m ∈ Finset.univ.erase m₀, Row.dd P F d m / Row.D P F d m with hSdef
  have hqI := Row.qI (F := F)
  have hr0 := Row.r_nonneg hP d
  have hr1 := Row.r_le_one hP d
  have hS : S ≤ Row.r P F d - Row.dd P F d m₀ / Row.M F + 1 / 2 -
      (Row.M F - Row.q F * Row.N P F d m₀) / Row.M F := by
    have hrow : ∀ m, Row.dd P F d m / Row.D P F d m ≤
        (Row.dd P F d m + Row.q F * Row.u P F d m) / Row.M F := fun m => by
      have hu := Row.u_le_half hP hc m
      have hu0 := Row.u_nonneg (F := F) d m
      have hq0 := Row.q_nonneg (F := F)
      refine Row.budget_real _ _ _ _ hM (Row.dd_nonneg d m) (mul_nonneg hq0 hu0) ?_ ?_
      · have := mul_le_mul_of_nonneg_left (show Row.u P F d m ≤ Row.I F by
          linarith [Row.I_pos (F := F)]) hq0
        linarith
      · simp only [Row.D, Row.N]
        rw [Row.nonce_card hP]
        nlinarith [Row.dd_le_a (F := F) d m]
    have hfree : ∑ m, Row.dd P F d m ≤ Row.v P F d := by
      simp only [Row.dd, Row.v]
      exact_mod_cast sum_rowFree_le P F d
    have hU := Row.sum_u_le hP hc
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ m₀)] at hfree hU
    calc S ≤ ∑ m ∈ Finset.univ.erase m₀, (Row.dd P F d m + Row.q F * Row.u P F d m) / Row.M F :=
          Finset.sum_le_sum fun m _ => hrow m
      _ = ((∑ m ∈ Finset.univ.erase m₀, Row.dd P F d m) +
            Row.q F * ∑ m ∈ Finset.univ.erase m₀, Row.u P F d m) / Row.M F := by
          rw [← Finset.sum_div, Finset.sum_add_distrib, Finset.mul_sum]
      _ ≤ (Row.v P F d - Row.dd P F d m₀ + Row.q F * (Row.I F / 2 - Row.u P F d m₀)) / Row.M F := by
          gcongr
          · linarith
          · exact Row.q_nonneg
          · linarith
      _ = _ := by
          simp only [Row.N, Row.r]
          rw [Row.nonce_card hP]
          have e : Row.q F * (Row.I F / 2 - Row.u P F d m₀) =
              Row.M F / 2 - Row.q F * Row.u P F d m₀ := by rw [← hqI]; ring
          have e' : Row.q F * (Row.I F - Row.u P F d m₀) = Row.M F - Row.q F * Row.u P F d m₀ := by
            rw [← hqI]; ring
          rw [e, e']
          field_simp
          ring
  have hx1 : max (Row.x P F d m₀) 0 ≤ (1 - Row.r P F d) * Row.a P F d m₀ := by
    refine max_le ?_ (mul_nonneg (by linarith) (Row.a_nonneg d m₀))
    simp only [Row.x]
    nlinarith [Row.b_le_a (F := F) d m₀]
  have key := RowIneq.charge_le (Row.M F) (Row.I F) (Row.a P F d m₀) (Row.dd P F d m₀)
    (Row.q F * Row.N P F d m₀) (max (Row.x P F d m₀) 0) (Row.r P F d) S hM (by linarith)
    (Row.qN_ge hP hc m₀) (Row.qN_le hP hc m₀) (Row.a_nonneg d m₀) (Row.dd_nonneg d m₀)
    (Row.dd_le_a d m₀) hr0 hr1 (le_max_right _ _) hx1 (Row.one_le_D hP hc m₀) hMI2 hS
  rw [show Row.M F / Row.I F = Row.q F from rfl,
    show Row.a P F d m₀ + Row.q F * Row.N P F d m₀ = Row.D P F d m₀ from rfl] at key
  have e4 : (Row.r P F d * Row.M F * (1 - Row.r P F d) + Row.dd P F d m₀) / Row.D P F d m₀ =
      Row.v P F d * B + Row.dd P F d m₀ / Row.D P F d m₀ := by
    rw [Row.rM hP, hB]; ring
  rw [hA]
  linarith [key, e4]

end Classes

/-! ## The charge and the domination -/

theorem ofReal_two_pow (k : ℕ) : ENNReal.ofReal ((2 : ℝ) ^ k) = (2 : ℝ≥0∞) ^ k := by
  rw [ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]

theorem natCast_div_two_pow (n k : ℕ) :
    ((n : ℝ≥0∞) / 2 ^ k) = ENNReal.ofReal ((n : ℝ) / 2 ^ k) := by
  rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_natCast, ofReal_two_pow]

namespace Row

variable {P F}

theorem θ_bounds (hP : RowHyp P F) : 1 ≤ θ F ∧ θ F ≤ 12 / 11 := by
  have hL := hP.trial_le
  have hL' : 24 * (F.trialLimit : ℝ) ≤ I F := by unfold I; exact_mod_cast hL
  have hL0 : (0 : ℝ) ≤ F.trialLimit := Nat.cast_nonneg _
  have hpos : 0 < I F - 2 * F.trialLimit := by linarith [I_pos (F := F)]
  unfold θ
  constructor
  · rw [le_div_iff₀ hpos]; linarith
  · rw [div_le_iff₀ hpos]; linarith

end Row

section Charge

variable {P F} (hP : RowHyp P F) {d : Cache P} (hc : 2 * encCount P F d ≤ 2 ^ F.idxBits)
include hP hc

theorem sum_idxOf (f : ℕ → ℝ) :
    ∑ w : BitVec P.hashBits, f (idxOf P F w) =
      (2 : ℝ) ^ (P.hashBits - F.idxBits) * ∑ i ∈ Finset.range (2 ^ F.idxBits), f i := by
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.range (2 ^ F.idxBits))
    (g := idxOf P F) (fun w _ => Finset.mem_range.2 (idxOf_lt P F w)), Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.sum_congr rfl (g := fun _ => f i) (fun w hw => by rw [(Finset.mem_filter.1 hw).2]),
    Finset.sum_const, nsmul_eq_mul]
  have := card_idxOf_mem P F hP.idx_le {i} (by simpa using Finset.mem_range.1 hi)
  simp only [Finset.mem_singleton, Finset.card_singleton, one_mul] at this
  rw [this]
  push_cast
  ring

theorem psi_avg {m₀ : Message P} {η₀ : Nonce F} (hfresh : d (encQuery P F (m₀ ++ η₀)) = none) :
    (∑ w : BitVec P.hashBits, psi P F (d.cacheQuery (encQuery P F (m₀ ++ η₀)) w)) /
        (2 : ℝ) ^ P.hashBits ≤ psi P F d + 11 / 6 / Row.I F := by
  have hK : (2 : ℝ) ^ P.hashBits = Row.I F * 2 ^ (P.hashBits - F.idxBits) := by
    unfold Row.I; rw [← pow_add, Nat.add_sub_cancel' hP.idx_le]
  have hKpos : (0 : ℝ) < 2 ^ P.hashBits := by positivity
  rw [div_le_iff₀ hKpos]
  calc ∑ w : BitVec P.hashBits, psi P F (d.cacheQuery (encQuery P F (m₀ ++ η₀)) w)
      ≤ ∑ w : BitVec P.hashBits, (psi P F d + gCls P F d m₀ (idxOf P F w)) :=
        Finset.sum_le_sum fun w _ => psi_step hP hc hfresh w
    _ = (2 : ℝ) ^ P.hashBits * psi P F d + (2 : ℝ) ^ (P.hashBits - F.idxBits) *
          ∑ i ∈ Finset.range (2 ^ F.idxBits), gCls P F d m₀ i := by
        rw [Finset.sum_add_distrib, sum_idxOf hP hc, Finset.sum_const, Finset.card_univ,
          Fintype.card_bitVec, nsmul_eq_mul]
        push_cast; ring
    _ ≤ (2 : ℝ) ^ P.hashBits * psi P F d + (2 : ℝ) ^ (P.hashBits - F.idxBits) * (11 / 6) := by
        gcongr
        exact sum_gCls_le hP hc m₀
    _ = (psi P F d + 11 / 6 / Row.I F) * 2 ^ P.hashBits := by
        rw [hK]
        have := (Row.I_pos (F := F)).ne'
        field_simp

/-- One fresh encoding answer raises `θ psi` by at most `2 / 2^idxBits` on average. -/
theorem psi_charge {m₀ : Message P} {η₀ : Nonce F} (hfresh : d (encQuery P F (m₀ ++ η₀)) = none) :
    ∑ w, (Fintype.card (BitVec P.hashBits) : ℝ≥0∞)⁻¹ *
        ENNReal.ofReal (Row.θ F * psi P F (d.cacheQuery (encQuery P F (m₀ ++ η₀)) w)) ≤
      ENNReal.ofReal (Row.θ F * psi P F d) + 2 * ((2 : ℝ≥0∞) ^ F.idxBits)⁻¹ := by
  obtain ⟨hθ1, hθ2⟩ := Row.θ_bounds hP
  have hθ0 : 0 ≤ Row.θ F := by linarith
  have hKpos : (0 : ℝ) < 2 ^ P.hashBits := by positivity
  have hIpos := Row.I_pos (F := F)
  have hcard : (Fintype.card (BitVec P.hashBits) : ℝ≥0∞)⁻¹ =
      ENNReal.ofReal ((2 : ℝ) ^ P.hashBits)⁻¹ := by
    rw [ENNReal.ofReal_inv_of_pos hKpos, ofReal_two_pow, Fintype.card_bitVec]
    push_cast; rfl
  have h2 : 2 * ((2 : ℝ≥0∞) ^ F.idxBits)⁻¹ = ENNReal.ofReal (2 / Row.I F) := by
    rw [ENNReal.ofReal_div_of_pos hIpos, ENNReal.ofReal_ofNat, Row.I, ofReal_two_pow,
      div_eq_mul_inv]
  rw [hcard, h2]
  simp_rw [← ENNReal.ofReal_mul (inv_nonneg.2 hKpos.le)]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun w _ => mul_nonneg (inv_nonneg.2 hKpos.le)
      (mul_nonneg hθ0 (psi_nonneg P F hP _))),
    ← ENNReal.ofReal_add (mul_nonneg hθ0 (psi_nonneg P F hP d)) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have hav := psi_avg hP hc hfresh
  rw [← Finset.mul_sum, ← Finset.mul_sum, ← div_eq_inv_mul, mul_comm (Row.θ F) _]
  calc (∑ w, psi P F (d.cacheQuery (encQuery P F (m₀ ++ η₀)) w)) * Row.θ F / 2 ^ P.hashBits
      = (∑ w, psi P F (d.cacheQuery (encQuery P F (m₀ ++ η₀)) w)) / 2 ^ P.hashBits * Row.θ F := by
        ring
    _ ≤ (psi P F d + 11 / 6 / Row.I F) * Row.θ F := mul_le_mul_of_nonneg_right hav hθ0
    _ ≤ Row.θ F * psi P F d + 2 / Row.I F := by
        have : Row.θ F * (11 / 6 / Row.I F) ≤ 2 / Row.I F := by
          rw [mul_div_assoc', div_le_div_iff_of_pos_right hIpos]; linarith
        nlinarith

/-- `θ psi` bounds the signing loss of every row (the hypothesis of `signRho_bound`). -/
theorem psi_dom (m : Message P) (c : ℕ) (hc1 : (rowFresh P F d m).card ≤ c + F.trialLimit)
    (hc2 : c ≤ (rowFresh P F d m).card) :
    ((rowBad P F d m).card : ℝ≥0∞) + c * (((V P F d).card : ℝ≥0∞) / 2 ^ F.idxBits) ≤
      ENNReal.ofReal (Row.θ F * psi P F d) *
        ((rowAcc P F d m).card + c * ((F.numSets : ℝ≥0∞) / 2 ^ F.idxBits)) := by
  obtain ⟨hθ1, -⟩ := Row.θ_bounds hP
  have hIpos := Row.I_pos (F := F)
  have hM := Row.M_pos hP
  have hfreshN : ((rowFresh P F d m).card : ℝ) = Row.N P F d m := by
    have h1 : rowFresh P F d m = Finset.univ \ rowCached P F d m := by
      ext η; simp [rowFresh, rowCached]
    have h2 : (rowFresh P F d m).card + (rowCached P F d m).card = 2 ^ F.nonceBits := by
      rw [h1, Finset.card_sdiff_add_card_eq_card (Finset.subset_univ _), Finset.card_univ,
        Fintype.card_bitVec]
    have h3 : ((rowFresh P F d m).card : ℝ) + (rowCached P F d m).card = 2 ^ F.nonceBits := by
      exact_mod_cast h2
    simp only [Row.N, Row.u]; linarith
  have hNge := Row.N_ge hP hc m
  have hDpos := Row.D_pos hP hc m
  have hc1' : Row.N P F d m ≤ c + F.trialLimit := by rw [← hfreshN]; exact_mod_cast hc1
  have hc2' : (c : ℝ) ≤ Row.N P F d m := by rw [← hfreshN]; exact_mod_cast hc2
  have hL0 : (0 : ℝ) ≤ F.trialLimit := Nat.cast_nonneg _
  have hLI : 24 * (F.trialLimit : ℝ) ≤ Row.I F := by
    unfold Row.I; exact_mod_cast hP.trial_le
  have hc0 : (0 : ℝ) ≤ c := Nat.cast_nonneg _
  have hθ0 : (0 : ℝ) ≤ Row.θ F := by linarith
  have hq0 : 0 ≤ Row.q F := Row.q_nonneg
  have hr0 : 0 ≤ Row.r P F d := Row.r_nonneg hP d
  have ha0 : 0 ≤ Row.a P F d m := Row.a_nonneg d m
  have hpsi : Row.r P F d + max (Row.x P F d m) 0 / Row.D P F d m ≤ psi P F d := by
    unfold psi
    have := Finset.single_le_sum (f := Row.pr P F d) (fun m _ => Row.pr_nonneg d m)
      (Finset.mem_univ m)
    have hpm : Row.pr P F d m = max (Row.x P F d m) 0 / Row.D P F d m := rfl
    linarith
  have hNc : Row.N P F d m ≤ Row.θ F * c := by
    have hpos : 0 < Row.I F - 2 * F.trialLimit := by linarith
    simp only [Row.θ]
    rw [div_mul_eq_mul_div, le_div_iff₀ hpos]
    nlinarith [mul_le_mul_of_nonneg_left (show Row.N P F d m - F.trialLimit ≤ c by linarith)
      hIpos.le, mul_nonneg hL0 (show 0 ≤ 2 * Row.N P F d m - Row.I F by linarith)]
  have hDle : Row.D P F d m ≤ Row.θ F * (Row.a P F d m + c * Row.q F) := by
    have h1 := mul_le_mul_of_nonneg_left hNc hq0
    have h2 := mul_le_mul_of_nonneg_right hθ1 ha0
    simp only [Row.D]
    nlinarith
  have hx : Row.x P F d m ≤
      Row.θ F * (Row.a P F d m + c * Row.q F) * (max (Row.x P F d m) 0 / Row.D P F d m) := by
    calc Row.x P F d m ≤ max (Row.x P F d m) 0 := le_max_left _ _
      _ = Row.D P F d m * (max (Row.x P F d m) 0 / Row.D P F d m) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hDle (div_nonneg (le_max_right _ _) hDpos.le)
  have hapos : 0 ≤ Row.a P F d m + c * Row.q F := add_nonneg ha0 (mul_nonneg hc0 hq0)
  have hreal : Row.b P F d m + c * (Row.v P F d / 2 ^ F.idxBits) ≤
      Row.θ F * psi P F d * (Row.a P F d m + c * ((F.numSets : ℝ) / 2 ^ F.idxBits)) := by
    have hv : Row.v P F d / 2 ^ F.idxBits = Row.r P F d * Row.q F := by
      have : (F.numSets : ℝ) ≠ 0 := hM.ne'
      simp only [Row.r, Row.q, Row.I, Row.M]
      field_simp
    have hq' : (F.numSets : ℝ) / 2 ^ F.idxBits = Row.q F := rfl
    rw [hv, hq']
    have hxdef : Row.x P F d m = Row.b P F d m - Row.r P F d * Row.a P F d m := rfl
    have h1 := mul_le_mul_of_nonneg_left hpsi (mul_nonneg hθ0 hapos)
    have h2 := mul_le_mul_of_nonneg_right hθ1 (mul_nonneg hr0 hapos)
    nlinarith
  have hvnn : (0 : ℝ) ≤ c * (Row.v P F d / 2 ^ F.idxBits) :=
    mul_nonneg hc0 (div_nonneg (Row.v_nonneg d) (by positivity))
  have hL : ((rowBad P F d m).card : ℝ≥0∞) + c * (((V P F d).card : ℝ≥0∞) / 2 ^ F.idxBits) =
      ENNReal.ofReal (((rowBad P F d m).card : ℝ) + c * (((V P F d).card : ℝ) / 2 ^ F.idxBits)) := by
    rw [ENNReal.ofReal_add (Nat.cast_nonneg _) (mul_nonneg hc0 (by positivity)),
      ENNReal.ofReal_mul hc0, ENNReal.ofReal_natCast, ENNReal.ofReal_natCast, natCast_div_two_pow]
  have hR : ENNReal.ofReal (Row.θ F * psi P F d) *
      ((rowAcc P F d m).card + c * ((F.numSets : ℝ≥0∞) / 2 ^ F.idxBits)) =
      ENNReal.ofReal (Row.θ F * psi P F d *
        (((rowAcc P F d m).card : ℝ) + c * ((F.numSets : ℝ) / 2 ^ F.idxBits))) := by
    rw [ENNReal.ofReal_mul (mul_nonneg hθ0 (psi_nonneg P F hP d)),
      ENNReal.ofReal_add (Nat.cast_nonneg _) (mul_nonneg hc0 (by positivity)),
      ENNReal.ofReal_mul hc0, ENNReal.ofReal_natCast, ENNReal.ofReal_natCast, natCast_div_two_pow]
  rw [hL, hR]
  exact ENNReal.ofReal_le_ofReal hreal

end Charge

end OptimalOTS
