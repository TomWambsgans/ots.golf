import Submissions.Lower.AnalysisDefs

/-!
# The rank found by the nonce search

With a uniform nonce table and a ranking that gives each rank below `L₀` to exactly one index
value, the best rank found among `T` distinct nonces is `ℓ` with probability
`(1 - ℓ / N) ^ T - (1 - (ℓ + 1) / N) ^ T`, where `N = 2 ^ idxBits`.
-/

open OracleSpec OracleComp ENNReal

noncomputable section

open scoped Classical

namespace OptimalOTS

namespace Analysis

/-- Number of functions whose values on a set `S` all satisfy `p`. -/
theorem card_filter_forall_mem {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B]
    (S : Finset A) (p : B → Prop) [DecidablePred p] :
    (Finset.univ.filter fun f : A → B => ∀ a ∈ S, p (f a)).card =
      (Finset.univ.filter p).card ^ S.card * Fintype.card B ^ (Fintype.card A - S.card) := by
  have h : (Finset.univ.filter fun f : A → B => ∀ a ∈ S, p (f a)) =
      Fintype.piFinset (fun a => if a ∈ S then Finset.univ.filter p else Finset.univ) := by
    ext f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · intro hf a
      split_ifs with ha
      · simpa using hf a ha
      · simp
    · intro hf a ha
      simpa [ha] using hf a
  rw [h, Fintype.card_piFinset]
  simp only [apply_ite Finset.card]
  rw [Finset.prod_ite]
  simp only [Finset.prod_const, Finset.card_univ]
  congr 2
  · congr 1
    ext a; simp
  · rw [Finset.filter_not, Finset.card_sdiff_of_subset (Finset.filter_subset _ _)]
    congr 1
    congr 1
    ext a; simp

theorem idxOfOut_lt (P : Params) (y : BitVec P.hashBits) : idxOfOut P y < 2 ^ P.idxBits :=
  (y.setWidth P.idxBits).isLt

/-- Number of oracle outputs whose index lies in a set of index values. -/
theorem card_idxOfOut_mem {P : Params} (hidx : P.idxBits ≤ P.hashBits) (A : Finset ℕ)
    (hA : ∀ n ∈ A, n < 2 ^ P.idxBits) :
    (Finset.univ.filter fun y : BitVec P.hashBits => idxOfOut P y ∈ A).card =
      A.card * 2 ^ (P.hashBits - P.idxBits) := by
  have hH : 2 ^ P.hashBits = 2 ^ P.idxBits * 2 ^ (P.hashBits - P.idxBits) := by
    rw [← pow_add, Nat.add_sub_cancel' hidx]
  have hNpos : 0 < 2 ^ P.idxBits := by positivity
  rw [← Finset.card_range (2 ^ (P.hashBits - P.idxBits)), ← Finset.card_product]
  refine Finset.card_nbij' (fun y => (y.toNat % 2 ^ P.idxBits, y.toNat / 2 ^ P.idxBits))
    (fun x => BitVec.ofNat P.hashBits (x.1 + 2 ^ P.idxBits * x.2)) ?_ ?_ ?_ ?_
  · intro y hy
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hy
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_range]
    refine ⟨?_, ?_⟩
    · simpa [idxOfOut, BitVec.toNat_setWidth] using hy
    · rw [Nat.div_lt_iff_lt_mul hNpos]
      have := y.isLt
      rw [hH] at this
      linarith
  · intro x hx
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_range] at hx
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
    have h1 : x.1 + 2 ^ P.idxBits * x.2 < 2 ^ P.hashBits := by
      rw [hH]
      have := hA _ hx.1
      nlinarith
    simp only [idxOfOut, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (hA _ hx.1)]
    exact hx.1
  · intro y _
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat]
    rw [Nat.mod_add_div, Nat.mod_eq_of_lt y.isLt]
  · intro x hx
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_range] at hx
    have hx1 := hA _ hx.1
    have h1 : x.1 + 2 ^ P.idxBits * x.2 < 2 ^ P.hashBits := by
      rw [hH]
      nlinarith
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt hx1, Nat.add_mul_div_left _ _ hNpos, Nat.div_eq_of_lt hx1, zero_add]

theorem bestPure_eq_some_iff {P : Params} (T : ℕ) (rk : ℕ → Option ℕ)
    (w : Nonce P → BitVec P.hashBits) (ℓ : ℕ) :
    bestPure P T rk w = some ℓ ↔
      (∀ k < T, ∀ ℓ' < ℓ, rk (idxOfOut P (w (BitVec.ofNat P.nonceBits k))) ≠ some ℓ') ∧
      ∃ k < T, rk (idxOfOut P (w (BitVec.ofNat P.nonceBits k))) = some ℓ := by
  unfold bestPure
  rw [List.min?_eq_some_iff]
  simp only [List.mem_filterMap, List.mem_range]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun k hk ℓ' hℓ' h => ?_, h1⟩
    have := h2 ℓ' ⟨k, hk, h⟩
    omega
  · rintro ⟨h1, h2⟩
    refine ⟨h2, fun b ⟨k, hk, h⟩ => ?_⟩
    by_contra hb
    exact h1 k hk b (by omega) h

theorem sum_bestPure_eq {P : Params} (T : ℕ) (hT : T ≤ 2 ^ P.nonceBits)
    (hidx : P.idxBits ≤ P.hashBits) (rk : ℕ → Option ℕ) (L₀ : ℕ)
    (hrk : ∀ ℓ < L₀, ∃! n, n < 2 ^ P.idxBits ∧ rk n = some ℓ)
    (hrk' : ∀ n ℓ, rk n = some ℓ → ℓ < L₀) (ℓ : ℕ) (hℓ : ℓ < L₀) :
    (∑ w : Nonce P → BitVec P.hashBits, if bestPure P T rk w = some ℓ then (1 : ℝ≥0∞) else 0) /
        (Fintype.card (Nonce P → BitVec P.hashBits) : ℝ≥0∞) =
      ENNReal.ofReal
        ((1 - (ℓ : ℝ) / 2 ^ P.idxBits) ^ T - (1 - ((ℓ : ℝ) + 1) / 2 ^ P.idxBits) ^ T) := by
  obtain ⟨N, hN⟩ : ∃ N, N = 2 ^ P.idxBits := ⟨_, rfl⟩
  obtain ⟨M, hM⟩ : ∃ M, M = 2 ^ (P.hashBits - P.idxBits) := ⟨_, rfl⟩
  have hH : 2 ^ P.hashBits = N * M := by rw [hN, hM, ← pow_add, Nat.add_sub_cancel' hidx]
  let low : ℕ → Finset ℕ := fun s => (Finset.range N).filter fun n => ∃ ℓ' < s, rk n = some ℓ'
  have hlow : ∀ s ≤ L₀, (low s).card = s := by
    intro s hs
    suffices (low s).card = (Finset.range s).card by simpa using this
    refine Finset.card_bij (fun n _ => (rk n).getD 0) ?_ ?_ ?_
    · intro n hn
      simp only [low, Finset.mem_filter, Finset.mem_range] at hn
      obtain ⟨-, ℓ', hℓ', h⟩ := hn
      simp [h, hℓ']
    · intro n hn n' hn' h
      simp only [low, Finset.mem_filter, Finset.mem_range] at hn hn'
      obtain ⟨hn, ℓ', hℓ', h1⟩ := hn
      obtain ⟨hn', ℓ'', hℓ'', h2⟩ := hn'
      simp only [h1, h2, Option.getD_some] at h
      subst h
      exact (hrk ℓ' (by omega)).unique ⟨hN ▸ hn, h1⟩ ⟨hN ▸ hn', h2⟩
    · intro b hb
      rw [Finset.mem_range] at hb
      obtain ⟨n, ⟨hn, h⟩, -⟩ := hrk b (by omega)
      refine ⟨n, ?_, by simp [h]⟩
      simp only [low, Finset.mem_filter, Finset.mem_range]
      exact ⟨hN ▸ hn, b, hb, h⟩
  have hL₀N : L₀ ≤ N := by
    have := Finset.card_filter_le (Finset.range N) fun n => ∃ ℓ' < L₀, rk n = some ℓ'
    rw [Finset.card_range] at this
    exact (hlow L₀ le_rfl) ▸ this
  let S := (Finset.range T).image (BitVec.ofNat P.nonceBits)
  have hS : S.card = T := by
    rw [Finset.card_image_of_injOn, Finset.card_range]
    intro k hk k' hk' h
    simp only [Finset.coe_range, Set.mem_Iio] at hk hk'
    have := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat] at this
    rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
  let G : ℕ → Finset (Nonce P → BitVec P.hashBits) := fun s =>
    Finset.univ.filter fun w => ∀ a ∈ S, idxOfOut P (w a) ∉ low s
  have hGmem : ∀ s w, w ∈ G s ↔
      ∀ k < T, ∀ ℓ' < s, rk (idxOfOut P (w (BitVec.ofNat P.nonceBits k))) ≠ some ℓ' := by
    intro s w
    simp [G, S, low, hN, idxOfOut_lt]
  have hG : ∀ s ≤ L₀, (G s).card = ((N - s) * M) ^ T * (N * M) ^ (2 ^ P.nonceBits - T) := by
    intro s hs
    have hc : (G s).card = (Finset.univ.filter fun y : BitVec P.hashBits =>
        idxOfOut P y ∉ low s).card ^ S.card *
          Fintype.card (BitVec P.hashBits) ^ (Fintype.card (Nonce P) - S.card) := by
      convert card_filter_forall_mem S (fun y : BitVec P.hashBits => idxOfOut P y ∉ low s)
    rw [hc, hS, Fintype.card_bitVec, Fintype.card_bitVec, hH]
    congr 2
    have h1 := Finset.card_filter_add_card_filter_not (s := Finset.univ)
      (fun y : BitVec P.hashBits => idxOfOut P y ∈ low s)
    rw [card_idxOfOut_mem hidx (low s) (fun n hn => by
      simp only [low, Finset.mem_filter, Finset.mem_range] at hn; exact hN ▸ hn.1),
      hlow s hs, Finset.card_univ, Fintype.card_bitVec, hH, ← hM] at h1
    rw [Nat.sub_mul]
    omega
  have hsub : G (ℓ + 1) ⊆ G ℓ := by
    intro w hw
    rw [hGmem] at hw ⊢
    exact fun k hk ℓ' hℓ' => hw k hk ℓ' (by omega)
  have hbest : Finset.univ.filter (fun w => bestPure P T rk w = some ℓ) = G ℓ \ G (ℓ + 1) := by
    ext w
    rw [Finset.mem_filter, bestPure_eq_some_iff, Finset.mem_sdiff, hGmem, hGmem]
    simp only [Finset.mem_univ, true_and]
    constructor
    · rintro ⟨h1, k, hk, h⟩
      exact ⟨h1, fun h2 => h2 k hk ℓ (by omega) h⟩
    · rintro ⟨h1, h2⟩
      push Not at h2
      obtain ⟨k, hk, ℓ', hℓ', h⟩ := h2
      refine ⟨h1, k, hk, ?_⟩
      rcases Nat.lt_or_ge ℓ' ℓ with h3 | h3
      · exact absurd h (h1 k hk ℓ' h3)
      · rwa [show ℓ = ℓ' by omega]
  have hle := Finset.card_le_card hsub
  rw [Finset.sum_boole, hbest, Finset.card_sdiff_of_subset hsub]
  rw [hG ℓ hℓ.le, hG (ℓ + 1) hℓ] at hle ⊢
  rw [Fintype.card_fun, Fintype.card_bitVec, Fintype.card_bitVec, hH]
  have hNpos : (0 : ℝ) < N := by rw [hN]; positivity
  have hMpos : (0 : ℝ) < M := by rw [hM]; positivity
  have hℓN : ℓ + 1 ≤ N := by omega
  have key : (1 - (ℓ : ℝ) / 2 ^ P.idxBits) ^ T - (1 - ((ℓ : ℝ) + 1) / 2 ^ P.idxBits) ^ T =
      ((((N - ℓ) * M) ^ T * (N * M) ^ (2 ^ P.nonceBits - T) -
        ((N - (ℓ + 1)) * M) ^ T * (N * M) ^ (2 ^ P.nonceBits - T) : ℕ) : ℝ) /
        (((N * M) ^ 2 ^ P.nonceBits : ℕ) : ℝ) := by
    have h2 : (2 : ℝ) ^ P.idxBits = N := by rw [hN]; push_cast; rfl
    rw [Nat.cast_sub hle, _root_.eq_div_iff (by push_cast; positivity), h2]
    have hK : 2 ^ P.nonceBits = T + (2 ^ P.nonceBits - T) := (Nat.add_sub_cancel' hT).symm
    rw [hK, pow_add]
    simp only [Nat.add_sub_cancel_left]
    push_cast [Nat.cast_sub (show ℓ ≤ N by omega), Nat.cast_sub hℓN]
    have e1 : (1 - (ℓ : ℝ) / N) * (N * M) = (N - ℓ) * M := by field_simp
    have e2 : (1 - ((ℓ : ℝ) + 1) / N) * (N * M) = (N - (ℓ + 1)) * M := by field_simp
    rw [← e1, ← e2]
    generalize (1 - (ℓ : ℝ) / N) = a
    generalize (1 - ((ℓ : ℝ) + 1) / N) = b
    ring
  rw [key, ENNReal.ofReal_div_of_pos (by push_cast; positivity), ENNReal.ofReal_natCast,
    ENNReal.ofReal_natCast]

end Analysis

end OptimalOTS
