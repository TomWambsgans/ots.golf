import Submissions.DisclosureLower.CacheFresh
import Submissions.DisclosureLower.Index
import Submissions.DisclosureLower.CostCore
import Submissions.DisclosureLower.SignFresh

/-! Consecutive nonce trials, with exact success bounds when the nonce does not wrap. -/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal
noncomputable section
open scoped Classical

namespace OptimalOTS.PatternSearch

/-- Try `k` consecutive nonces from `start`, modulo the nonce space, until a target is hit. -/
def search (P : Params) (G : Finset ℕ) (m : Message P) :
    ℕ → ℕ → OracleComp (Spec P) (Option (Nonce P × ℕ))
  | 0, _ => pure none
  | k + 1, start =>
    (liftM ((Spec P).query (.inr (encQuery P (m ++ BitVec.ofNat P.nonceBits start)))) :
      OracleComp (Spec P) (BitVec P.hashBits)) >>= fun w =>
        if idxOf P w ∈ G then pure (some (BitVec.ofNat P.nonceBits start, idxOf P w))
        else search P G m k (start + 1)

/-- Each trial costs one index query, even if the cache already has its answer. -/
theorem cost_search {P : Params} (hidx : idxCost P = 1) (G : Finset ℕ) (m : Message P) :
    ∀ k start, CostAtMost P (search P G m k start) k
  | 0, _ => costAtMost_pure _ _
  | k + 1, start => by
    rw [search, costAtMost_query_bind_iff]
    have hq : queryCost P (.inr (encQuery P (m ++ BitVec.ofNat P.nonceBits start))) = 1 := hidx
    rw [hq, Nat.add_sub_cancel]
    refine ⟨by omega, fun w => ?_⟩
    split_ifs
    · exact costAtMost_pure _ _
    · exact cost_search hidx G m k (start + 1)

/-- A successful output names a target and a cached answer for its nonce query. -/
theorem search_support {P : Params} (G : Finset ℕ) (m : Message P) :
    ∀ k start c p, p ∈ support (run P (search P G m k start) c) →
      ∀ η j, p.1 = some (η, j) → j ∈ G ∧
        ∃ w, p.2 (encQuery P (m ++ η)) = some w ∧ idxOf P w = j := by
  intro k
  induction k with
  | zero =>
    intro start c p hp η j hout
    rw [search, run_pure, support_pure] at hp
    simp only [Set.mem_singleton_iff] at hp
    subst hp
    simp at hout
  | succ k ih =>
    intro start c p hp η j hout
    rw [search] at hp
    rcases hc : c (encQuery P (m ++ BitVec.ofNat P.nonceBits start)) with _ | w
    · obtain ⟨w, hp⟩ := mem_support_run_inr_none P hc hp
      by_cases hw : idxOf P w ∈ G
      · rw [if_pos hw, run_pure, support_pure] at hp
        simp only [Set.mem_singleton_iff] at hp
        subst hp
        simp only [Option.some.injEq, Prod.mk.injEq] at hout
        obtain ⟨rfl, rfl⟩ := hout
        exact ⟨hw, w, QueryCache.cacheQuery_self _ _ _, rfl⟩
      · rw [if_neg hw] at hp
        exact ih _ _ _ hp η j hout
    · have hp := mem_support_run_inr_some P hc hp
      by_cases hw : idxOf P w ∈ G
      · rw [if_pos hw, run_pure, support_pure] at hp
        simp only [Set.mem_singleton_iff] at hp
        subst hp
        simp only [Option.some.injEq, Prod.mk.injEq] at hout
        obtain ⟨rfl, rfl⟩ := hout
        exact ⟨hw, w, hc, rfl⟩
      · rw [if_neg hw] at hp
        exact ih _ _ _ hp η j hout

/-- All nonce queries in the remaining trial interval are absent from the cache. -/
def FreshRange {P : Params} (c : Cache P) (m : Message P) (start k : ℕ) : Prop :=
  ∀ n, start ≤ n → n < start + k →
    c (encQuery P (m ++ BitVec.ofNat P.nonceBits n)) = none

theorem freshRange_of_freshMessage {P : Params} {c : Cache P} {m : Message P}
    (h : BareLower.FreshMessage c m) (start k : ℕ) : FreshRange c m start k :=
  fun _ _ _ => h _

theorem FreshRange.step {P : Params} {c : Cache P} {m : Message P} {start k : ℕ}
    (hc : FreshRange c m start (k + 1)) (hbound : start + (k + 1) ≤ 2 ^ P.nonceBits)
    (w : BitVec P.hashBits) :
    FreshRange (c.cacheQuery (encQuery P (m ++ BitVec.ofNat P.nonceBits start)) w)
      m (start + 1) k := by
  intro n hn hn'
  have hne : encQuery P (m ++ BitVec.ofNat P.nonceBits n) ≠
      encQuery P (m ++ BitVec.ofNat P.nonceBits start) := by
    intro heq
    have heq := append_nonce_inj P m (encQuery_inj P heq)
    have heq := congrArg BitVec.toNat heq
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show n < 2 ^ P.nonceBits by omega),
      Nat.mod_eq_of_lt (show start < 2 ^ P.nonceBits by omega)] at heq
    omega
  rw [QueryCache.cacheQuery_of_ne _ _ hne]
  exact hc n (by omega) (by omega)

/-- A uniform oracle output hits `G` with the expected index fraction. -/
theorem uniform_target {P : Params} (hidx : P.idxBits ≤ P.hashBits)
    (G : Finset ℕ) (hG : ∀ j ∈ G, j < 2 ^ P.idxBits) :
    E ($ᵗ BitVec P.hashBits) (fun w => if idxOf P w ∈ G then 1 else 0) =
      (G.card : ℝ≥0∞) / 2 ^ P.idxBits := by
  have heq : E ($ᵗ BitVec P.hashBits) (fun w => if idxOf P w ∈ G then 1 else 0) =
      ((Finset.univ.filter fun w : BitVec P.hashBits => idxOf P w ∈ G).card : ℝ≥0∞) /
        2 ^ P.hashBits := by
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using
      BareLower.uniform_indicator P.hashBits (Finset.univ.filter fun w => idxOf P w ∈ G)
  rw [heq, show (Finset.univ.filter fun w : BitVec P.hashBits => idxOf P w ∈ G).card =
      G.card * 2 ^ (P.hashBits - P.idxBits) from Analysis.card_idxOfOut_mem hidx G hG]
  push_cast
  rw [show (2 : ℝ≥0∞) ^ P.hashBits =
      2 ^ P.idxBits * 2 ^ (P.hashBits - P.idxBits) by
        rw [← pow_add, Nat.add_sub_cancel' hidx]]
  exact ENNReal.mul_div_mul_right _ _ (by simp) (by simp)

/-- The complementary single-trial probability. -/
theorem uniform_miss {P : Params} (hidx : P.idxBits ≤ P.hashBits)
    (G : Finset ℕ) (hG : ∀ j ∈ G, j < 2 ^ P.idxBits) :
    E ($ᵗ BitVec P.hashBits) (fun w => if idxOf P w ∈ G then 0 else 1) =
      1 - (G.card : ℝ≥0∞) / 2 ^ P.idxBits := by
  apply ENNReal.eq_sub_of_add_eq' (by simp)
  rw [← uniform_target hidx G hG, E, E, ← expectedValue_add]
  have heq : (fun w : BitVec P.hashBits =>
      (if idxOf P w ∈ G then (0 : ℝ≥0∞) else 1) +
      (if idxOf P w ∈ G then (1 : ℝ≥0∞) else 0)) = fun _ => (1 : ℝ≥0∞) := by
    funext w
    by_cases hw : idxOf P w ∈ G <;> simp only [hw, if_true, if_false, zero_add, add_zero]
  rw [heq, expectedValue_const (by simp)]

/-- Exact all-trials-fail probability for fresh, distinct nonce queries. -/
theorem failure_eq {P : Params} (hidx : P.idxBits ≤ P.hashBits)
    (G : Finset ℕ) (hG : ∀ j ∈ G, j < 2 ^ P.idxBits) (m : Message P) :
    ∀ k start c, start + k ≤ 2 ^ P.nonceBits → FreshRange c m start k →
      E (run P (search P G m k start) c) (fun p => if p.1.isSome then 0 else 1) =
        (1 - (G.card : ℝ≥0∞) / 2 ^ P.idxBits) ^ k := by
  intro k
  induction k with
  | zero =>
    intro start c hb hc
    rw [search, run_pure, E_pure]
    simp
  | succ k ih =>
    intro start c hb hc
    have hc0 := hc start le_rfl (by omega)
    rw [search, run_query_bind, oracleImpl_run_inr_none P hc0, E_bind]
    simp only [E_bind, E_pure]
    have heq : (fun w : BitVec P.hashBits =>
        E (run P (if idxOf P w ∈ G then pure (some (BitVec.ofNat P.nonceBits start, idxOf P w))
          else search P G m k (start + 1))
          (c.cacheQuery (encQuery P (m ++ BitVec.ofNat P.nonceBits start)) w))
          (fun p => if p.1.isSome then 0 else 1)) =
        (fun w => (if idxOf P w ∈ G then (0 : ℝ≥0∞) else 1) *
          (1 - (G.card : ℝ≥0∞) / 2 ^ P.idxBits) ^ k) := by
      funext w
      by_cases hw : idxOf P w ∈ G
      · rw [if_pos hw, run_pure, E_pure, if_pos hw]
        simp
      · rw [if_neg hw, if_neg hw, one_mul]
        exact ih (start + 1) _ (by omega) (hc.step hb w)
    rw [heq, E, expectedValue_mul_const]
    have hu := uniform_miss hidx G hG
    simp only [E] at hu
    rw [hu, pow_succ, mul_comm]

/-- Exact search success probability. -/
theorem success_eq {P : Params} (hidx : P.idxBits ≤ P.hashBits)
    (G : Finset ℕ) (hG : ∀ j ∈ G, j < 2 ^ P.idxBits) (m : Message P)
    (k start : ℕ) (c : Cache P) (hb : start + k ≤ 2 ^ P.nonceBits)
    (hc : FreshRange c m start k) :
    E (run P (search P G m k start) c) (fun p => if p.1.isSome then 1 else 0) =
      1 - (1 - (G.card : ℝ≥0∞) / 2 ^ P.idxBits) ^ k := by
  apply ENNReal.eq_sub_of_add_eq' (by simp)
  rw [← failure_eq hidx G hG m k start c hb hc, E, E, ← expectedValue_add]
  have heq : (fun p : Option (Nonce P × ℕ) × Cache P =>
      (if p.1.isSome then (1 : ℝ≥0∞) else 0) +
      (if p.1.isSome then (0 : ℝ≥0∞) else 1)) = fun _ => (1 : ℝ≥0∞) := by
    funext p
    cases p.1 <;> simp
  rw [heq, expectedValue_const (by simp)]

attribute [irreducible] search

end OptimalOTS.PatternSearch
