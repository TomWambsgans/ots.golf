import Submissions.GenericLower.Costs
import VCVio.EvalDist.Expectation

/-! Zero-cost generic verification is independent of the random-oracle cache. -/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal
noncomputable section
open scoped Classical

namespace OptimalOTS.GenericLower

abbrev Cache (P : Params) := (hashSpec P).QueryCache
abbrev run (P : Params) {α : Type} (oa : OracleComp (Spec P) α) (c : Cache P) :
    ProbComp (α × Cache P) := (simulateQ (oracleImpl P) oa).run c
abbrev E {α : Type} (p : ProbComp α) (f : α → ℝ≥0∞) := expectedValue p f

/-- Keep private randomness and replace every hash answer by zero. -/
def freeImpl (P : Params) : QueryImpl (Spec P) ProbComp :=
  HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp) +
    (show QueryImpl (hashSpec P) ProbComp from fun _ => pure (0 : BitVec P.hashBits))

def freeRun (P : Params) {α : Type} (oa : OracleComp (Spec P) α) : ProbComp α :=
  simulateQ (freeImpl P) oa

theorem run_pure (P : Params) {α : Type} (x : α) (c : Cache P) :
    run P (pure x) c = pure (x, c) := by simp [run]

theorem run_bind (P : Params) {α β : Type} (oa : OracleComp (Spec P) α)
    (k : α → OracleComp (Spec P) β) (c : Cache P) :
    run P (oa >>= k) c = run P oa c >>= fun p => run P (k p.1) p.2 := by
  simp only [run, simulateQ_bind, StateT.run_bind]

theorem run_map (P : Params) {α β : Type} (oa : OracleComp (Spec P) α)
    (f : α → β) (c : Cache P) :
    run P (f <$> oa) c = (fun p => (f p.1, p.2)) <$> run P oa c := by
  simp only [run, simulateQ_map, StateT.run_map]

/-- A zero-cost program never hashes, so its output is independent of the unchanged cache. -/
theorem run_zero (P : Params) {α : Type} (oa : OracleComp (Spec P) α)
    (h : CostAtMost P oa 0) (c : Cache P) :
    run P oa c = (fun x => (x, c)) <$> freeRun P oa := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp [run_pure, freeRun]
  | query_bind t k ih =>
    unfold CostAtMost at h
    rw [isQueryBound_query_bind_iff] at h
    have hb := h
    cases t with
    | inr q =>
      have hcost := hb.1
      change blockCost P q.1 ≤ 0 at hcost
      unfold blockCost at hcost
      omega
    | inl t =>
      have hk : ∀ u, CostAtMost P (k u) 0 := by
        intro u
        simpa [CostAtMost, queryCost] using hb.2 u
      simp only [run, simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      have hl : (oracleImpl P (.inl t)).run c =
          HasQuery.query (spec := unifSpec) (m := ProbComp) t >>= fun u => pure (u, c) := by
        simp [oracleImpl, StateT.run_monadLift]
      rw [hl]
      simp only [bind_assoc, pure_bind]
      simp only [freeRun, simulateQ_bind, simulateQ_spec_query, freeImpl, QueryImpl.add_apply_inl]
      rw [map_bind]
      congr 1
      funext u
      exact ih u (hk u)

abbrev win (P : Params) (oa : OracleComp (Spec P) Bool) (c : Cache P) : ℝ≥0∞ :=
  Pr[= true | Prod.fst <$> run P oa c]

theorem probTrue_eq_win (P : Params) (oa : OracleComp (Spec P) Bool) :
    probTrue P oa = win P oa ∅ := by simp [probTrue, win, run, StateT.run'_eq]

theorem win_bind (P : Params) {α : Type} (oa : OracleComp (Spec P) α)
    (k : α → OracleComp (Spec P) Bool) (c : Cache P) :
    win P (oa >>= k) c = E (run P oa c) (fun x => win P (k x.1) x.2) := by
  rw [win, run_bind, map_bind, probOutput_bind_eq_expectedValue]

theorem win_pure (P : Params) (b : Bool) (c : Cache P) :
    win P (pure b) c = if b then 1 else 0 := by
  cases b <;> simp [win, run_pure]

theorem win_zero (P : Params) (oa : OracleComp (Spec P) Bool)
    (h : CostAtMost P oa 0) (c : Cache P) :
    win P oa c = Pr[= true | freeRun P oa] := by
  rw [win, run_zero P oa h]
  simp

theorem E_const {α : Type} (p : ProbComp α) (v : ℝ≥0∞) : E p (fun _ => v) = v :=
  expectedValue_const (by simp) v

theorem E_eq_zero_on_support {α : Type} (p : ProbComp α) (f : α → ℝ≥0∞)
    (h : E p f = 0) {x : α} (hx : x ∈ support p) : f x = 0 := by
  have ht : Pr[= x | p] * f x = 0 := (ENNReal.tsum_eq_zero.mp h) x
  exact (mul_eq_zero.mp ht).resolve_left ((probOutput_pos_iff p x).mpr hx).ne'

end OptimalOTS.GenericLower
