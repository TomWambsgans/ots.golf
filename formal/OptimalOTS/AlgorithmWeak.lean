import OptimalOTS.Algorithm

/-! Fresh-message security and the lower-bound statement for arbitrary oracle algorithms. -/

open OracleSpec OracleComp ENNReal
noncomputable section
open scoped Classical

namespace OptimalOTS
namespace AlgorithmScheme

variable {P : Params}

/-- The same generic experiment, counting only fresh-message forgeries (or failed signing). -/
def weakExperiment (S : AlgorithmScheme P) (A : S.Adversary) : OracleComp (Spec P) Bool := do
  let (pk, sk) ← S.keygen
  let (m₁, st) ← A.choose pk
  let σ₁ ← S.sign sk m₁
  let (m₂, σ₂) ← A.forge st σ₁
  let ok ← S.verify pk m₂ σ₂
  return ok && (σ₁.isNone || decide (m₂ ≠ m₁))

/-- Weak security has the same total-experiment cost accounting and security exponent. -/
def WeaklySecure (S : AlgorithmScheme P) : Prop :=
  ∀ (A : S.Adversary) (B : ℕ), CostAtMost P (S.weakExperiment A) B →
    probTrue P (S.weakExperiment A) < (B : ℝ≥0∞) / 2 ^ P.securityBits

namespace SecurityBridge

abbrev Outcome (S : AlgorithmScheme P) := Message P × Option S.Signature × Message P × S.Signature × Bool

def experimentRun (S : AlgorithmScheme P) (A : S.Adversary) : OracleComp (Spec P) (Outcome S) := do
  let (pk, sk) ← S.keygen
  let (m₁, st) ← A.choose pk
  let σ₁ ← S.sign sk m₁
  let (m₂, σ₂) ← A.forge st σ₁
  let ok ← S.verify pk m₂ σ₂
  return (m₁, σ₁, m₂, σ₂, ok)

def strongWin {S : AlgorithmScheme P} (r : Outcome S) : Bool :=
  r.2.2.2.2 && decide (r.2.1.map (fun s => (r.1, s)) ≠ some (r.2.2.1, r.2.2.2.1))

def weakWin {S : AlgorithmScheme P} (r : Outcome S) : Bool :=
  r.2.2.2.2 && (r.2.1.isNone || decide (r.2.2.1 ≠ r.1))

theorem experiment_eq_map (S : AlgorithmScheme P) (A : S.Adversary) :
    S.experiment A = strongWin <$> experimentRun S A := by
  simp only [AlgorithmScheme.experiment, experimentRun, strongWin, map_eq_bind_pure_comp,
    bind_assoc, pure_bind, Function.comp]

theorem weakExperiment_eq_map (S : AlgorithmScheme P) (A : S.Adversary) :
    S.weakExperiment A = weakWin <$> experimentRun S A := by
  simp only [weakExperiment, experimentRun, weakWin, map_eq_bind_pure_comp,
    bind_assoc, pure_bind, Function.comp]

theorem strongWin_of_weakWin {S : AlgorithmScheme P} (r : Outcome S)
    (h : weakWin r = true) : strongWin r = true := by
  obtain ⟨m₁, σ₁, m₂, σ₂, ok⟩ := r
  simp only [weakWin, strongWin, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h ⊢
  refine ⟨h.1, ?_⟩
  rcases h.2 with hnone | hne
  · cases σ₁ with
    | none => simp
    | some s => simp at hnone
  · cases σ₁ with
    | none => simp
    | some s =>
      intro heq
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at heq
      exact hne heq.1.symm

theorem cost_iff (S : AlgorithmScheme P) (A : S.Adversary) (B : ℕ) :
    CostAtMost P (S.experiment A) B ↔ CostAtMost P (S.weakExperiment A) B := by
  unfold CostAtMost
  rw [experiment_eq_map, weakExperiment_eq_map, isQueryBound_map_iff, isQueryBound_map_iff]

theorem weak_success_le (S : AlgorithmScheme P) (A : S.Adversary) :
    probTrue P (S.weakExperiment A) ≤ probTrue P (S.experiment A) := by
  unfold probTrue
  rw [experiment_eq_map, weakExperiment_eq_map, simulateQ_map, simulateQ_map, StateT.run'_map',
    StateT.run'_map', ← probEvent_eq_eq_probOutput, ← probEvent_eq_eq_probOutput,
    probEvent_map, probEvent_map]
  exact probEvent_mono'' fun r h => strongWin_of_weakWin r h

end SecurityBridge

/-- Every generic strongly secure scheme also meets fresh-message security. -/
theorem Secure.weaklySecure {S : AlgorithmScheme P} (h : S.Secure) : S.WeaklySecure := fun A B hB =>
  lt_of_le_of_lt (SecurityBridge.weak_success_le S A)
    (h A B ((SecurityBridge.cost_iff S A B).2 hB))

end AlgorithmScheme

/-- A universal lower bound for arbitrary algorithms under explicit resource and availability limits.
It rules out every pathwise verification budget below `c`, including all rejecting inputs. -/
def AlgorithmVerificationLowerBound (P : Params) (L : AlgorithmScheme.Limits) (ε : ℝ≥0∞)
    (c : ℕ) : Prop :=
  ∀ S : AlgorithmScheme P, S.Admissible L ε → S.WeaklySecure →
    ∀ v : ℕ, S.VerifyCostAtMost v → c ≤ v

end OptimalOTS
