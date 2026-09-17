import Submissions.Lower.CountingFactor

/-!
# The counting lemma

For each index `i`, `h i` is a nonnegative weight on a finite universe `U` that vanishes on the set
`V i`, and every `V i` has at most `a` elements. Call `i` good when its total weight is at most
`S`. Then few good indices have fewer than `R` indices `j` of weight `h i (V j) < d`: at most
`(R - 1) / β_a(d)` of them.

## Proof outline

Random orderings of `U` are formalized by `avgOrd`, the average over orderings built by choosing a
uniformly random first element and recursing. For a good index `i` we subtract a common amount `α`
from the weights (`exists_alpha`), so that at most `a ρ` reduced weights `w` are positive, and show
by induction on the universe (`core`) that some prefix containing `V i` has `w`-weight below
`b = d - a α` with probability at least `Phi`; the inductive step is `key_ineq`, which uses the
convexity of `fpoly` (Jensen). `Phi_ge_beta` bounds `Phi` below by the counting factor. Finally,
for a fixed ordering, the nesting of prefixes shows at most `R - 1` bad indices have such a prefix.
-/

open Finset
open scoped Classical

namespace OptimalOTS.CountingAux

noncomputable def fpoly (m : ℕ) (y : ℝ) : ℝ := ∏ k ∈ range m, (y + ((k:ℝ) + 1))

lemma fpoly_nonneg (m : ℕ) {y : ℝ} (hy : -1 ≤ y) : 0 ≤ fpoly m y :=
  prod_nonneg fun k _ => by have : (0:ℝ) ≤ k := k.cast_nonneg; linarith

lemma fpoly_pos (m : ℕ) {y : ℝ} (hy : -1 < y) : 0 < fpoly m y :=
  prod_pos fun k _ => by have : (0:ℝ) ≤ k := k.cast_nonneg; linarith

lemma fpoly_monotoneOn (m : ℕ) : MonotoneOn (fpoly m) (Set.Ici (-1)) := by
  intro x hx y _ hxy
  simp only [Set.mem_Ici] at hx
  exact prod_le_prod (fun k _ => by have : (0:ℝ) ≤ k := k.cast_nonneg; linarith)
    (fun k _ => by linarith)

lemma fpoly_convexOn (m : ℕ) : ConvexOn ℝ (Set.Ici (-1)) (fpoly m) := by
  induction m with
  | zero =>
    have : fpoly 0 = fun _ => 1 := by funext y; simp [fpoly]
    rw [this]; exact convexOn_const 1 (convex_Ici _)
  | succ m ih =>
    have : fpoly (m+1) = fpoly m * fun y => y + ((m:ℝ)+1) := by
      funext y; simp [fpoly, prod_range_succ]
    rw [this]
    apply ih.mul
    · exact (convexOn_id (convex_Ici _)).add (convexOn_const _ (convex_Ici _))
    · intro x hx; exact fpoly_nonneg m hx
    · intro x hx; simp only [Set.mem_Ici] at hx; have : (0:ℝ) ≤ m := m.cast_nonneg; linarith
    · exact (fpoly_monotoneOn m).monovaryOn (fun x _ y _ h => by linarith)

lemma fpoly_succ (m : ℕ) (y : ℝ) : fpoly (m+1) (y - 1) = y * fpoly m y := by
  simp only [fpoly]
  rw [prod_range_succ', mul_comm]
  congr 1
  · simp
  · apply prod_congr rfl; intro k _; push_cast; ring

lemma fpoly_neg_one (m : ℕ) : fpoly (m+1) (-1) = 0 := by
  have := fpoly_succ m 0; simpa using this

noncomputable def Phi (N : ℝ) (m : ℕ) (σ b : ℝ) : ℝ :=
  ∏ k ∈ range m, ((N * b - σ) / (σ + b) + ((k:ℝ) + 1)) / (N + ((k:ℝ) + 1))

lemma Phi_eq (N : ℝ) (m : ℕ) (σ b : ℝ) :
    Phi N m σ b = fpoly m ((N * b - σ) / (σ + b)) / fpoly m N := by
  simp only [Phi, fpoly, prod_div_distrib]

lemma cc_gt (N σ b : ℝ) (hN : 0 ≤ N) (hσ : 0 ≤ σ) (hb : 0 < b) :
    -1 < (N * b - σ) / (σ + b) := by
  rw [lt_div_iff₀ (by linarith)]; nlinarith

lemma Phi_nonneg (N : ℝ) (m : ℕ) (σ b : ℝ) (hN : 0 ≤ N) (hσ : 0 ≤ σ) (hb : 0 < b) :
    0 ≤ Phi N m σ b := by
  rw [Phi_eq]
  exact div_nonneg (fpoly_nonneg m (cc_gt N σ b hN hσ hb).le) (fpoly_nonneg m (by linarith))

lemma cc_add_one (N σ w b : ℝ) (hden : 0 < (σ - w) + (b - w)) :
    ((N - 1) * (b - w) - (σ - w)) / ((σ - w) + (b - w)) + 1
      = N * (b - w) / ((σ - w) + (b - w)) := by
  rw [div_add_one hden.ne']; congr 1; ring

lemma key_ineq {U : Type*} (P : Finset U) (w : U → ℝ) (hw : ∀ x ∈ P, 0 ≤ w x) (b : ℝ)
    (hb : 0 < b) (m : ℕ) :
    ((P.card : ℝ) + ((m : ℝ) + 1)) * Phi P.card (m + 1) (∑ x ∈ P, w x) b
      ≤ ((m : ℝ) + 1) * Phi P.card m (∑ x ∈ P, w x) b
        + ∑ x ∈ P, (if w x < b then
            Phi ((P.card : ℝ) - 1) (m + 1) ((∑ x ∈ P, w x) - w x) (b - w x) else 0) := by
  set N : ℝ := (P.card : ℝ) with hNdef
  set σ : ℝ := ∑ x ∈ P, w x with hσdef
  have hN0 : 0 ≤ N := Nat.cast_nonneg _
  have hσ : 0 ≤ σ := sum_nonneg hw
  have hwσ : ∀ x ∈ P, w x ≤ σ := fun x hx => single_le_sum hw hx
  set c := (N * b - σ) / (σ + b) with hc
  have hsucc : Phi N (m + 1) σ b = Phi N m σ b * ((c + ((m : ℝ) + 1)) / (N + ((m : ℝ) + 1))) := by
    simp only [Phi, prod_range_succ]; rfl
  have hNm : 0 < N + ((m : ℝ) + 1) := by have : (0:ℝ) ≤ m := m.cast_nonneg; linarith
  have hL : (N + ((m : ℝ) + 1)) * Phi N (m + 1) σ b = Phi N m σ b * (c + ((m : ℝ) + 1)) := by
    rw [hsucc]; field_simp
  rw [hL]
  have hLnn : ∀ x ∈ P, 0 ≤ (if w x < b then Phi (N - 1) (m + 1) (σ - w x) (b - w x) else 0) := by
    intro x hx
    split_ifs with h
    · apply Phi_nonneg
      · have : 1 ≤ N := by
          rw [hNdef]; exact_mod_cast Finset.card_pos.mpr ⟨x, hx⟩
        linarith
      · linarith [hwσ x hx]
      · linarith
    · exact le_refl _
  suffices h : c * Phi N m σ b ≤ ∑ x ∈ P, (if w x < b then
      Phi (N - 1) (m + 1) (σ - w x) (b - w x) else 0) by linarith
  by_cases hc0 : c ≤ 0
  · have := Phi_nonneg N m σ b hN0 hσ hb
    have := sum_nonneg hLnn
    nlinarith
  push Not at hc0
  have hNpos : 0 < N := by
    by_contra hN; push Not at hN
    have : N = 0 := le_antisymm hN hN0
    rw [hc, this] at hc0
    have : (0 * b - σ) / (σ + b) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
    linarith
  have hN1 : 1 ≤ N := by
    have : 0 < P.card := by have h := hNpos; rw [hNdef] at h; exact_mod_cast h
    rw [hNdef]; exact Nat.one_le_cast.mpr this
  have hD : 0 < fpoly (m + 1) (N - 1) := fpoly_pos _ (by linarith)
  -- express everything via fpoly
  let y : U → ℝ := fun x => if w x < b then
      ((N - 1) * (b - w x) - (σ - w x)) / ((σ - w x) + (b - w x)) else -1
  have hy1 : ∀ x ∈ P, -1 ≤ y x := by
    intro x hx
    simp only [y]
    split_ifs with h
    · have hden : 0 < (σ - w x) + (b - w x) := by linarith [hwσ x hx]
      have := cc_add_one N σ (w x) b hden
      have : 0 ≤ N * (b - w x) / ((σ - w x) + (b - w x)) :=
        div_nonneg (mul_nonneg hN0 (by linarith)) hden.le
      linarith
    · exact le_refl _
  have hterm : ∀ x ∈ P, (if w x < b then Phi (N - 1) (m + 1) (σ - w x) (b - w x) else 0)
      = fpoly (m + 1) (y x) / fpoly (m + 1) (N - 1) := by
    intro x hx
    simp only [y]
    split_ifs with h
    · rw [Phi_eq]
    · rw [fpoly_neg_one, zero_div]
  rw [sum_congr rfl hterm, ← sum_div, le_div_iff₀ hD]
  have hlhs : c * Phi N m σ b * fpoly (m + 1) (N - 1) = N * fpoly (m + 1) (c - 1) := by
    rw [fpoly_succ, fpoly_succ, Phi_eq, ← hc]
    have : 0 < fpoly m N := fpoly_pos m (by linarith)
    field_simp
  rw [hlhs]
  -- Jensen
  have hJ := (fpoly_convexOn (m + 1)).map_sum_le (t := P) (w := fun _ => 1 / N) (p := y)
    (fun _ _ => by positivity) (by rw [sum_const, nsmul_eq_mul, ← hNdef]; field_simp) hy1
  simp only [smul_eq_mul, ← mul_sum] at hJ
  have hmean : c - 1 ≤ 1 / N * ∑ x ∈ P, y x := by
    have hge : ∀ x ∈ P, N * (b - w x) / (σ + b) ≤ y x + 1 := by
      intro x hx
      simp only [y]
      split_ifs with h
      · have hden : 0 < (σ - w x) + (b - w x) := by linarith [hwσ x hx]
        rw [cc_add_one N σ (w x) b hden]
        apply div_le_div_of_nonneg_left (mul_nonneg hN0 (by linarith)) hden (by linarith [hw x hx])
      · have : N * (b - w x) / (σ + b) ≤ 0 :=
          div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hN0 (by linarith))
            (by linarith)
        linarith
    have hs := sum_le_sum hge
    rw [sum_add_distrib, sum_const, nsmul_eq_mul, mul_one, ← sum_div, ← mul_sum,
      sum_sub_distrib, sum_const, nsmul_eq_mul, ← hNdef, ← hσdef] at hs
    have hcN : N * c = N * (N * b - σ) / (σ + b) := by rw [hc]; ring
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hNpos]
    nlinarith
  have hmono := fpoly_monotoneOn (m + 1) (show c - 1 ∈ Set.Ici (-1) by simp; linarith)
    (show 1 / N * ∑ x ∈ P, y x ∈ Set.Ici (-1) by
      simp only [Set.mem_Ici]
      have := sum_le_sum hy1
      rw [sum_const, nsmul_eq_mul] at this
      rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hNpos]; linarith) hmean
  have := mul_le_mul_of_nonneg_left (hmono.trans hJ) hN0
  rw [← mul_assoc, mul_one_div_cancel hNpos.ne', one_mul] at this
  exact this

section Orderings

variable {U : Type*}

/-- Average over uniformly random orderings of `s`, built front to back. -/
noncomputable def avgOrd : ℕ → Finset U → (List U → ℝ) → ℝ
  | 0, _, F => F []
  | n + 1, s, F => (∑ x ∈ s, avgOrd n (s.erase x) (fun l => F (x :: l))) / s.card

lemma avgOrd_mono : ∀ (n : ℕ) (s : Finset U) (F G : List U → ℝ), (∀ l, F l ≤ G l) →
    avgOrd n s F ≤ avgOrd n s G
  | 0, _, _, _, h => h []
  | n + 1, _, _, _, h => div_le_div_of_nonneg_right
      (sum_le_sum fun _ _ => avgOrd_mono n _ _ _ fun _ => h _) (Nat.cast_nonneg _)

lemma avgOrd_nonneg : ∀ (n : ℕ) (s : Finset U) (F : List U → ℝ), (∀ l, 0 ≤ F l) →
    0 ≤ avgOrd n s F
  | 0, _, _, h => h []
  | n + 1, _, _, h => div_nonneg
      (sum_nonneg fun _ _ => avgOrd_nonneg n _ _ fun _ => h _) (Nat.cast_nonneg _)

lemma avgOrd_const : ∀ (n : ℕ) (s : Finset U) (c : ℝ), s.card = n → avgOrd n s (fun _ => c) = c
  | 0, _, _, _ => rfl
  | n + 1, s, c, hs => by
    simp only [avgOrd]
    rw [sum_congr rfl fun x hx => avgOrd_const n (s.erase x) c (by rw [card_erase_of_mem hx, hs]; rfl)]
    rw [sum_const, nsmul_eq_mul, hs]
    have : (0:ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
    field_simp

lemma avgOrd_sum {κ : Type*} (B : Finset κ) : ∀ (n : ℕ) (s : Finset U) (F : κ → List U → ℝ),
    avgOrd n s (fun l => ∑ i ∈ B, F i l) = ∑ i ∈ B, avgOrd n s (F i)
  | 0, _, _ => rfl
  | n + 1, s, F => by
    simp only [avgOrd]
    rw [sum_congr rfl fun x _ => avgOrd_sum B n (s.erase x) (fun i l => F i (x :: l))]
    rw [sum_comm, sum_div]

/-- Some prefix of `l` contains `V` and has `w`-weight below `b`. -/
def Q (w : U → ℝ) (V : Finset U) (b : ℝ) (l : List U) : Prop :=
  ∃ k, V ⊆ (l.take k).toFinset ∧ ∑ g ∈ (l.take k).toFinset, w g < b

lemma Q_empty (w : U → ℝ) (b : ℝ) (hb : 0 < b) (l : List U) : Q w ∅ b l :=
  ⟨0, by simp, by simpa using hb⟩

lemma Q_cons (w : U → ℝ) (hw : ∀ g, 0 ≤ w g) (V : Finset U) (b : ℝ) (x : U) (l : List U)
    (h : Q w (V.erase x) (b - w x) l) : Q w V b (x :: l) := by
  obtain ⟨k, hV, hs⟩ := h
  refine ⟨k + 1, ?_, ?_⟩
  · rw [List.take_succ_cons, List.toFinset_cons, subset_insert_iff]; exact hV
  · rw [List.take_succ_cons, List.toFinset_cons]
    calc ∑ g ∈ insert x (l.take k).toFinset, w g ≤ w x + ∑ g ∈ (l.take k).toFinset, w g := by
          by_cases hx : x ∈ (l.take k).toFinset
          · rw [insert_eq_of_mem hx]; linarith [hw x]
          · rw [sum_insert hx]
      _ < b := by linarith

theorem core (w : U → ℝ) (hw : ∀ g, 0 ≤ w g) : ∀ (n : ℕ) (s : Finset U), s.card = n →
    ∀ V : Finset U, V ⊆ s → (∀ g ∈ V, w g = 0) → ∀ b : ℝ, 0 < b →
    Phi ((s.filter fun g => 0 < w g).card : ℝ) V.card (∑ g ∈ s, w g) b
      ≤ avgOrd n s (fun l => if Q w V b l then 1 else 0) := by
  intro n
  induction n with
  | zero =>
    intro s hs V hV _ b hb
    have hs0 : s = ∅ := card_eq_zero.mp hs
    subst hs0
    have : V = ∅ := subset_empty.mp hV
    subst this
    simp [Phi, avgOrd, Q_empty w b hb]
  | succ n ih =>
    intro s hs V hV hV0 b hb
    by_cases hVe : V = ∅
    · subst hVe
      simp only [Q_empty w b hb, if_true, card_empty, Phi, prod_range_zero]
      rw [avgOrd_const _ _ _ hs]
    obtain ⟨m, hm⟩ : ∃ m, V.card = m + 1 :=
      Nat.exists_eq_succ_of_ne_zero (by rwa [Ne, card_eq_zero])
    set P := s.filter fun g => 0 < w g with hP
    set Z := s.filter fun g => ¬ 0 < w g with hZ
    set σ := ∑ g ∈ s, w g with hσ
    set N : ℝ := (P.card : ℝ) with hN
    let L : U → ℝ := fun x => if w x < b then
      Phi (((s.erase x).filter fun g => 0 < w g).card : ℝ) (V.erase x).card
        (∑ g ∈ s.erase x, w g) (b - w x) else 0
    have hLle : ∀ x ∈ s,
        L x ≤ avgOrd n (s.erase x) (fun l => if Q w V b (x :: l) then 1 else 0) := by
      intro x hx
      simp only [L]
      split_ifs with hxb
      · refine (ih (s.erase x) (by rw [card_erase_of_mem hx, hs]; rfl) (V.erase x)
          (erase_subset_erase x hV) (fun g hg => hV0 g (mem_of_mem_erase hg)) (b - w x)
          (by linarith)).trans ?_
        apply avgOrd_mono
        intro l
        by_cases h1 : Q w (V.erase x) (b - w x) l
        · rw [if_pos h1, if_pos (Q_cons w hw V b x l h1)]
        · rw [if_neg h1]; split_ifs <;> norm_num
      · exact avgOrd_nonneg _ _ _ (fun l => by split_ifs <;> norm_num)
    simp only [avgOrd]
    rw [hs, le_div_iff₀ (by positivity)]
    refine le_trans ?_ (sum_le_sum hLle)
    rw [← sum_filter_add_sum_filter_not s (fun g => 0 < w g)]
    have hVZ : V ⊆ Z := by
      intro g hg; rw [hZ, mem_filter]; exact ⟨hV hg, by rw [hV0 g hg]; exact lt_irrefl 0⟩
    rw [← hP, ← hZ, ← sum_sdiff hVZ]
    have hZterm : ∀ x ∈ Z, L x = Phi N (V.erase x).card σ b := by
      intro x hx
      rw [hZ, mem_filter] at hx
      have hwx : w x = 0 := le_antisymm (not_lt.mp hx.2) (hw x)
      simp only [L, hwx, hb, if_true, sub_zero]
      rw [filter_erase, erase_eq_of_notMem (by rw [mem_filter]; exact fun h => hx.2 h.2),
        sum_erase s hwx]
    have hV' : ∀ x ∈ V, L x = Phi N m σ b := by
      intro x hx
      rw [hZterm x (hVZ hx), card_erase_of_mem hx, hm]; rfl
    have hZV' : ∀ x ∈ Z \ V, L x = Phi N (m + 1) σ b := by
      intro x hx
      rw [mem_sdiff] at hx
      rw [hZterm x hx.1, erase_eq_of_notMem hx.2, hm]
    have hP' : ∀ x ∈ P, L x = if w x < b then
        Phi (N - 1) (m + 1) ((∑ g ∈ P, w g) - w x) (b - w x) else 0 := by
      intro x hx
      have hx' := mem_filter.mp hx
      have hxV : x ∉ V := fun h => by rw [hV0 x h] at hx'; exact lt_irrefl 0 hx'.2
      simp only [L]
      rw [filter_erase, ← hP, card_erase_of_mem hx, erase_eq_of_notMem hxV, hm,
        sum_erase_eq_sub hx'.1]
      have hsP : ∑ g ∈ P, w g = σ := by
        rw [hP, sum_filter_of_ne]
        intro g _ hg; exact lt_of_le_of_ne (hw g) (Ne.symm hg)
      have hPpos : 1 ≤ P.card := card_pos.mpr ⟨x, hx⟩
      rw [hsP, Nat.cast_sub hPpos, Nat.cast_one]
    rw [sum_congr rfl hP', sum_congr rfl hV', sum_congr rfl hZV', sum_const, sum_const,
      nsmul_eq_mul, nsmul_eq_mul, hm]
    have hkey := key_ineq P w (fun x _ => hw x) b hb m
    have hsP : ∑ g ∈ P, w g = σ := by
      rw [hP, sum_filter_of_ne]
      intro g _ hg; exact lt_of_le_of_ne (hw g) (Ne.symm hg)
    rw [← hN, hsP] at hkey
    have hcnt : ((Z \ V).card : ℝ) + ((m : ℝ) + 1) + N = ((n + 1 : ℕ) : ℝ) := by
      have h1 := card_sdiff_add_card_eq_card hVZ
      have h2 := card_filter_add_card_filter_not (s := s) (fun g => 0 < w g)
      rw [← hP, ← hZ] at h2
      rw [hm] at h1
      rw [hN]
      have : (Z \ V).card + (m + 1) + P.card = n + 1 := by omega
      exact_mod_cast this
    rw [← hcnt, hsP]
    have hexp : Phi N (m + 1) σ b * (((Z \ V).card : ℝ) + ((m : ℝ) + 1) + N)
        = ((Z \ V).card : ℝ) * Phi N (m + 1) σ b + (N + ((m : ℝ) + 1)) * Phi N (m + 1) σ b := by
      ring
    rw [hexp]
    push_cast
    linarith [hkey]

end Orderings

section Final

lemma exists_alpha {U : Type*} [Fintype U] (h : U → ℝ) (hnn : ∀ g, 0 ≤ h g) (a : ℕ) (S d : ℝ)
    (hS : 0 < S) (hd : 0 < d) (hsum : ∑ g, h g ≤ S) :
    ∃ α : ℝ, 0 ≤ α ∧ (a : ℝ) * α < d ∧
      ((univ.filter fun g => α < h g).card : ℝ) ≤ a * (S / d) ∧
      ∑ g, max (h g - α) 0 ≤ (S / d) * (d - a * α) := by
  set n0 := ⌊(a : ℝ) * (S / d)⌋₊ with hn0
  have hρ : 0 < S / d := div_pos hS hd
  have hn0le : (n0 : ℝ) ≤ a * (S / d) := Nat.floor_le (by positivity)
  have hn0lt : (a : ℝ) * (S / d) < n0 + 1 := Nat.lt_floor_add_one _
  have hSρ : S = (S / d) * d := by field_simp
  set Cand := insert (0 : ℝ) (univ.image h) with hCand
  have hCnn : ∀ x ∈ Cand, 0 ≤ x := by
    intro x hx
    rw [hCand, mem_insert, mem_image] at hx
    rcases hx with rfl | ⟨g, _, rfl⟩
    · exact le_refl _
    · exact hnn g
  set C := Cand.filter fun x => (univ.filter fun g => x < h g).card ≤ n0 with hC
  have hCne : C.Nonempty := by
    refine ⟨Cand.max' (insert_nonempty _ _), ?_⟩
    rw [hC, mem_filter]
    refine ⟨max'_mem _ _, ?_⟩
    have : (univ.filter fun g => Cand.max' (insert_nonempty _ _) < h g) = ∅ := by
      rw [filter_eq_empty_iff]
      intro g _
      exact not_lt.mpr (le_max' _ _ (mem_insert_of_mem (mem_image_of_mem h (mem_univ g))))
    rw [this, card_empty]
    exact Nat.zero_le _
  set α := C.min' hCne with hα
  have hαC : α ∈ C := min'_mem _ _
  rw [hC, mem_filter] at hαC
  have hα0 : 0 ≤ α := hCnn _ hαC.1
  have hcard : ((univ.filter fun g => α < h g).card : ℝ) ≤ n0 := by exact_mod_cast hαC.2
  have hpt : ∀ g, max (h g - α) 0 + (if α ≤ h g then α else 0) ≤ h g := by
    intro g
    split_ifs with hg
    · rw [max_eq_left (by linarith)]; linarith
    · rw [max_eq_right (by linarith [not_le.mp hg])]; linarith [hnn g]
  have hsumw : ∑ g, max (h g - α) 0 + ((univ.filter fun g => α ≤ h g).card : ℝ) * α ≤ S := by
    have := sum_le_sum fun g (_ : g ∈ univ) => hpt g
    rw [sum_add_distrib, ← sum_filter, sum_const, nsmul_eq_mul] at this
    linarith
  have hwnn : 0 ≤ ∑ g, max (h g - α) 0 := sum_nonneg fun g _ => le_max_right _ _
  by_cases hαz : α = 0
  · refine ⟨α, hα0, by rw [hαz, mul_zero]; exact hd, by linarith, ?_⟩
    have : ∑ g, max (h g - α) 0 ≤ S := by
      have := mul_nonneg (Nat.cast_nonneg (α := ℝ) (univ.filter fun g => α ≤ h g).card) hα0
      linarith
    rw [hαz, mul_zero, sub_zero, ← hSρ]
    rw [hαz] at this
    exact this
  · have hαp : 0 < α := lt_of_le_of_ne hα0 (Ne.symm hαz)
    have hbig : n0 + 1 ≤ (univ.filter fun g => α ≤ h g).card := by
      by_contra hlt
      rw [not_le] at hlt
      set T := Cand.filter fun x => x < α with hT
      have hTne : T.Nonempty := ⟨0, by rw [hT, mem_filter]; exact ⟨mem_insert_self _ _, hαp⟩⟩
      set α' := T.max' hTne with hα'
      have hα'T := max'_mem T hTne
      rw [← hα', hT, mem_filter] at hα'T
      have hα'C : α' ∈ C := by
        rw [hC, mem_filter]
        refine ⟨hα'T.1, le_trans (card_le_card ?_) (Nat.lt_succ_iff.mp hlt)⟩
        intro g hg
        rw [mem_filter] at hg ⊢
        refine ⟨mem_univ _, ?_⟩
        by_contra hng
        rw [not_le] at hng
        have hgT : h g ∈ T := by
          rw [hT, mem_filter]
          exact ⟨mem_insert_of_mem (mem_image_of_mem h (mem_univ g)), hng⟩
        have := le_max' T (h g) hgT
        rw [← hα'] at this
        linarith [hg.2]
      have := min'_le C α' hα'C
      rw [← hα] at this
      linarith [hα'T.2]
    have hbigR : (n0 : ℝ) + 1 ≤ ((univ.filter fun g => α ≤ h g).card : ℝ) := by
      exact_mod_cast hbig
    have h1 : ((n0 : ℝ) + 1) * α ≤ ((univ.filter fun g => α ≤ h g).card : ℝ) * α :=
      mul_le_mul_of_nonneg_right hbigR hα0
    have h2 : (a : ℝ) * (S / d) * α < ((n0 : ℝ) + 1) * α := mul_lt_mul_of_pos_right hn0lt hαp
    refine ⟨α, hα0, ?_, by linarith, ?_⟩
    · -- a α (S/d) < S = (S/d) d
      have : (S / d) * ((a : ℝ) * α) < (S / d) * d := by
        rw [← hSρ]; nlinarith
      exact lt_of_mul_lt_mul_left this hρ.le
    · have : (S / d) * (d - a * α) = S - (a : ℝ) * (S / d) * α := by
        rw [mul_sub, ← hSρ]; ring
      rw [this]
      linarith

lemma factor_mono (a : ℕ) (ρ N : ℝ) (hρ : 0 < ρ) (hN : 0 ≤ N) (hNa : N ≤ a * ρ) (k : ℕ) :
    (((a : ℝ) - 1) * ρ / (1 + ρ) + ((k : ℝ) + 1)) / ((a : ℝ) * ρ + ((k : ℝ) + 1))
      ≤ ((N - ρ) / (1 + ρ) + ((k : ℝ) + 1)) / (N + ((k : ℝ) + 1)) := by
  have hk : (0 : ℝ) ≤ k := k.cast_nonneg
  have e1 : ((a : ℝ) - 1) * ρ / (1 + ρ) + ((k : ℝ) + 1)
      = (((a : ℝ) - 1) * ρ + ((k : ℝ) + 1) * (1 + ρ)) / (1 + ρ) := by
    field_simp
  have e2 : (N - ρ) / (1 + ρ) + ((k : ℝ) + 1) = ((N - ρ) + ((k : ℝ) + 1) * (1 + ρ)) / (1 + ρ) := by
    field_simp
  rw [e1, e2, div_div, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
  have hA : 0 ≤ (a : ℝ) * ρ - N := by linarith
  have hB : 0 ≤ ρ * k := by positivity
  have := mul_nonneg (mul_nonneg hA hB) (by linarith : (0:ℝ) ≤ 1 + ρ)
  nlinarith [this]

lemma Phi_ge_beta (a : ℕ) (ha : 1 ≤ a) (S d : ℝ) (hS : 0 < S) (hd : 0 < d) (N : ℝ) (hN : 0 ≤ N)
    (hNa : N ≤ a * (S / d)) (m : ℕ) (hm : m ≤ a) (σ b : ℝ) (hσ : 0 ≤ σ) (hb : 0 < b)
    (hσb : σ ≤ (S / d) * b) : countingFactor a S d ≤ Phi N m σ b := by
  set ρ := S / d with hρdef
  have hρ : 0 < ρ := div_pos hS hd
  set c := (N * b - σ) / (σ + b) with hc
  have hc1 : -1 < c := cc_gt N σ b hN hσ hb
  have hfac_nn : ∀ k : ℕ, 0 ≤ (c + ((k : ℝ) + 1)) / (N + ((k : ℝ) + 1)) := fun k =>
    div_nonneg (by have : (0:ℝ) ≤ k := k.cast_nonneg; linarith) (by positivity)
  have hfac_le : ∀ k : ℕ, (c + ((k : ℝ) + 1)) / (N + ((k : ℝ) + 1)) ≤ 1 := by
    intro k
    rw [div_le_one (by positivity)]
    have : c ≤ N := by
      rw [hc, div_le_iff₀ (by linarith)]; nlinarith
    linarith
  have hstep1 : Phi N a σ b ≤ Phi N m σ b := by
    simp only [Phi]
    rw [← prod_range_mul_prod_Ico _ hm, ← hc]
    have h0 : 0 ≤ ∏ k ∈ range m, (c + ((k : ℝ) + 1)) / (N + ((k : ℝ) + 1)) :=
      prod_nonneg fun k _ => hfac_nn k
    have h1 : ∏ k ∈ Ico m a, (c + ((k : ℝ) + 1)) / (N + ((k : ℝ) + 1)) ≤ 1 :=
      prod_le_one (fun k _ => hfac_nn k) (fun k _ => hfac_le k)
    calc _ ≤ (∏ k ∈ range m, (c + ((k : ℝ) + 1)) / (N + ((k : ℝ) + 1))) * 1 :=
          mul_le_mul_of_nonneg_left h1 h0
      _ = _ := mul_one _
  refine le_trans ?_ hstep1
  simp only [countingFactor, Phi]
  rw [← hρdef, ← hc]
  apply prod_le_prod
  · intro k _
    have hk : (0 : ℝ) ≤ k := k.cast_nonneg
    have ha' : (1 : ℝ) ≤ a := by exact_mod_cast ha
    have h1 : 0 ≤ ((a : ℝ) - 1) * ρ / (1 + ρ) :=
      div_nonneg (mul_nonneg (by linarith) hρ.le) (by linarith)
    have h2 := mul_nonneg (Nat.cast_nonneg (α := ℝ) a) hρ.le
    exact div_nonneg (by linarith) (by linarith)
  · intro k _
    refine le_trans (factor_mono a ρ N hρ hN hNa k) ?_
    apply div_le_div_of_nonneg_right _ (by positivity)
    have : (N - ρ) / (1 + ρ) ≤ c := by
      rw [hc, div_le_div_iff₀ (by linarith) (by linarith)]
      have := mul_le_mul_of_nonneg_left hσb (by linarith : (0:ℝ) ≤ N + 1)
      nlinarith
    linarith

lemma countingFactor_pos (a : ℕ) (ha : 1 ≤ a) (S d : ℝ) (hS : 0 < S) (hd : 0 < d) :
    0 < countingFactor a S d := by
  have hρ : 0 < S / d := div_pos hS hd
  have ha' : (1 : ℝ) ≤ a := by exact_mod_cast ha
  apply prod_pos
  intro k _
  have hk : (0 : ℝ) ≤ k := k.cast_nonneg
  have : 0 ≤ ((a : ℝ) - 1) * (S / d) / (1 + S / d) :=
    div_nonneg (mul_nonneg (by linarith) hρ.le) (by linarith)
  apply div_pos (by linarith) (by positivity)

end Final

end OptimalOTS.CountingAux

namespace OptimalOTS

open CountingAux

/-- The counting lemma (Lemma 4 of the paper). Indices `j` are counted separately even when their
sets `V j` coincide. -/
theorem card_few_low_weight_targets_le
    {ι U : Type*} [Fintype ι] [Fintype U]
    (V : ι → Finset U) (a : ℕ) (ha : 1 ≤ a) (hV : ∀ i, (V i).card ≤ a)
    (h : ι → U → ℝ) (h_nonneg : ∀ i g, 0 ≤ h i g) (h_zero : ∀ i, ∀ g ∈ V i, h i g = 0)
    (S d : ℝ) (hS : 0 < S) (hd : 0 < d) (R : ℕ) (hR : 1 ≤ R) :
    ((Finset.univ.filter fun i =>
        ∑ g, h i g ≤ S ∧ (Finset.univ.filter fun j => ∑ g ∈ V j, h i g < d).card < R).card : ℝ)
      ≤ ((R : ℝ) - 1) / countingFactor a S d := by
  have hβ : 0 < countingFactor a S d := countingFactor_pos a ha S d hS hd
  rw [le_div_iff₀ hβ]
  set B := (Finset.univ.filter fun i =>
        ∑ g, h i g ≤ S ∧ (Finset.univ.filter fun j => ∑ g ∈ V j, h i g < d).card < R) with hB
  let Ui : ι → List U → Prop := fun i l => ∃ k, V i ⊆ (l.take k).toFinset ∧
    ∀ j, V j ⊆ (l.take k).toFinset → ∑ g ∈ V j, h i g < d
  have hcount : ∀ l : List U, ∑ i ∈ B, (if Ui i l then (1 : ℝ) else 0) ≤ (R : ℝ) - 1 := by
    intro l
    rw [sum_boole]
    have hlt : (B.filter fun i => Ui i l).card < R := by
      by_contra hge
      rw [not_lt] at hge
      set T := B.filter fun i => Ui i l with hT
      have hTne : T.Nonempty := card_pos.mp (by omega)
      let K : ι → ℕ := fun i => if hi : Ui i l then Classical.choose hi else 0
      obtain ⟨i, hiT, hmax⟩ := exists_max_image T K hTne
      have hiT' := mem_filter.mp hiT
      have hiB := (mem_filter.mp hiT'.1).2
      have hKi : Ui i l := hiT'.2
      have hspec := Classical.choose_spec hKi
      have hsub : T ⊆ univ.filter fun j => ∑ g ∈ V j, h i g < d := by
        intro j hj
        have hj' := mem_filter.mp hj
        have hspecj := Classical.choose_spec hj'.2
        rw [mem_filter]
        refine ⟨mem_univ _, hspec.2 j ?_⟩
        have hKj := hmax j hj
        simp only [K, dif_pos hj'.2, dif_pos hKi] at hKj
        intro g hg
        have hg' := hspecj.1 hg
        rw [List.mem_toFinset] at hg' ⊢
        exact List.take_subset_take_left l hKj hg'
      have := card_le_card hsub
      omega
    have : ((B.filter fun i => Ui i l).card : ℝ) + 1 ≤ R := by exact_mod_cast hlt
    linarith
  have hprob : ∀ i ∈ B, countingFactor a S d
      ≤ avgOrd (univ : Finset U).card univ (fun l => if Ui i l then 1 else 0) := by
    intro i hi
    obtain ⟨hgood, -⟩ := (mem_filter.mp hi).2
    obtain ⟨α, hα0, hαd, hcardα, hsumα⟩ :=
      exists_alpha (h i) (h_nonneg i) a S d hS hd hgood
    let w : U → ℝ := fun g => max (h i g - α) 0
    have hw : ∀ g, 0 ≤ w g := fun g => le_max_right _ _
    have hwV : ∀ g ∈ V i, w g = 0 := by
      intro g hg
      simp only [w, h_zero i g hg, zero_sub]
      exact max_eq_right (by linarith)
    have hcore := core w hw _ univ rfl (V i) (subset_univ _) hwV (d - a * α) (by linarith)
    have hpos : (univ.filter fun g => 0 < w g) = univ.filter fun g => α < h i g := by
      apply filter_congr
      intro g _
      simp only [w, lt_max_iff, lt_irrefl, or_false, sub_pos]
    rw [hpos] at hcore
    refine le_trans ?_ (hcore.trans ?_)
    · apply Phi_ge_beta a ha S d hS hd _ (Nat.cast_nonneg _) hcardα _ (hV i) _ _
        (sum_nonneg fun g _ => hw g) (by linarith) hsumα
    · apply avgOrd_mono
      intro l
      by_cases hq : Q w (V i) (d - a * α) l
      · obtain ⟨k, hk1, hk2⟩ := hq
        have hU : Ui i l := by
          refine ⟨k, hk1, fun j hj => ?_⟩
          calc ∑ g ∈ V j, h i g ≤ ∑ g ∈ V j, (α + w g) :=
                sum_le_sum fun g _ => by
                  have := le_max_left (h i g - α) 0
                  simp only [w]; linarith
            _ = (V j).card * α + ∑ g ∈ V j, w g := by
                rw [sum_add_distrib, sum_const, nsmul_eq_mul]
            _ ≤ a * α + ∑ g ∈ (l.take k).toFinset, w g := by
                have h1 : ((V j).card : ℝ) * α ≤ a * α :=
                  mul_le_mul_of_nonneg_right (by exact_mod_cast hV j) hα0
                have h2 := sum_le_sum_of_subset_of_nonneg hj (fun g _ _ => hw g)
                linarith
            _ < d := by linarith
        have hq' : Q w (V i) (d - a * α) l := ⟨k, hk1, hk2⟩
        rw [if_pos hq', if_pos hU]
      · rw [if_neg hq]
        split_ifs <;> norm_num
  calc (B.card : ℝ) * countingFactor a S d = ∑ i ∈ B, countingFactor a S d := by
        rw [sum_const, nsmul_eq_mul]
    _ ≤ ∑ i ∈ B, avgOrd (univ : Finset U).card univ (fun l => if Ui i l then 1 else 0) :=
        sum_le_sum hprob
    _ = avgOrd (univ : Finset U).card univ (fun l => ∑ i ∈ B, if Ui i l then 1 else 0) :=
        (avgOrd_sum B _ _ _).symm
    _ ≤ avgOrd (univ : Finset U).card univ (fun _ => (R : ℝ) - 1) := avgOrd_mono _ _ _ _ hcount
    _ = (R : ℝ) - 1 := avgOrd_const _ _ _ rfl

end OptimalOTS
