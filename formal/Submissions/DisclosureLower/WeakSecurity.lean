import OptimalOTS.Statement

/-!
# Weak unforgeability

The weak experiment runs the strong experiment's oracle calls and differs only in its winning
condition: an accepted forgery must use a new message when signing succeeds. Every weak win is a
strong win, so every secure scheme is weakly secure with the same budget and bound. The
lower-bound attacks forge on a new message and use this notion as their intermediate step.
-/

open OracleSpec OracleComp ENNReal

noncomputable section

open scoped Classical

namespace OptimalOTS

/-- Weak-forgery experiment. The attacker must produce an accepted signature on a different
message; after signing failure, any accepted pair wins. Every weak win is also a strong win. -/
def weakExperiment {P : Params} (S : Scheme P) (A : Adversary P) : OracleComp (Spec P) Bool := do
  let (pk, sk) ← S.keygen
  let (m₁, st) ← A.choose pk
  let σ₁ ← S.sign sk m₁
  let (m₂, σ₂) ← A.forge st σ₁
  let ok ← S.verify pk m₂ σ₂
  return ok && (σ₁.isNone || decide (m₂ ≠ m₁))

/-- Existential unforgeability with the same strict, total-experiment bound as `Secure`. Every
secure scheme is weakly secure (`Scheme.Secure.weaklySecure`); the lower-bound attacks forge on a
new message and use this notion as their intermediate step. -/
def Scheme.WeaklySecure {P : Params} (S : Scheme P) : Prop :=
  ∀ (A : Adversary P) (B : ℕ), CostAtMost P (weakExperiment S A) B →
    probTrue P (weakExperiment S A) < (B : ℝ≥0∞) / 2 ^ P.securityBits

namespace SchemeBridge

/-- The experiment's transcript: signed message, signature, forgery and verdict. -/
def experimentRun {P : Params} (S : Scheme P) (A : Adversary P) :
    OracleComp (Spec P) (Message P × Option (Signature P) × Message P × Signature P × Bool) := do
  let (pk, sk) ← S.keygen
  let (m₁, st) ← A.choose pk
  let σ₁ ← S.sign sk m₁
  let (m₂, σ₂) ← A.forge st σ₁
  let ok ← S.verify pk m₂ σ₂
  return (m₁, σ₁, m₂, σ₂, ok)

/-- The strong win condition on a transcript. -/
def strongWin {P : Params} (r : Message P × Option (Signature P) × Message P × Signature P × Bool) :
    Bool :=
  r.2.2.2.2 && decide (r.2.1.map (fun s => (r.1, s)) ≠ some (r.2.2.1, r.2.2.2.1))

/-- The weak win condition on a transcript. -/
def weakWin {P : Params} (r : Message P × Option (Signature P) × Message P × Signature P × Bool) :
    Bool :=
  r.2.2.2.2 && (r.2.1.isNone || decide (r.2.2.1 ≠ r.1))

theorem experiment_eq_map {P : Params} (S : Scheme P) (A : Adversary P) :
    experiment S A = strongWin <$> experimentRun S A := by
  simp only [experiment, experimentRun, strongWin, map_eq_bind_pure_comp, bind_assoc, pure_bind,
    Function.comp]

theorem weakExperiment_eq_map {P : Params} (S : Scheme P) (A : Adversary P) :
    weakExperiment S A = weakWin <$> experimentRun S A := by
  simp only [weakExperiment, experimentRun, weakWin, map_eq_bind_pure_comp, bind_assoc, pure_bind,
    Function.comp]

theorem strongWin_of_weakWin {P : Params}
    (r : Message P × Option (Signature P) × Message P × Signature P × Bool)
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

theorem cost_iff {P : Params} (S : Scheme P) (A : Adversary P) (B : ℕ) :
    CostAtMost P (experiment S A) B ↔ CostAtMost P (weakExperiment S A) B := by
  unfold CostAtMost
  rw [experiment_eq_map, weakExperiment_eq_map, isQueryBound_map_iff, isQueryBound_map_iff]

theorem weak_success_le {P : Params} (S : Scheme P) (A : Adversary P) :
    probTrue P (weakExperiment S A) ≤ probTrue P (experiment S A) := by
  unfold probTrue
  rw [experiment_eq_map, weakExperiment_eq_map, simulateQ_map, simulateQ_map, StateT.run'_map',
    StateT.run'_map', ← probEvent_eq_eq_probOutput, ← probEvent_eq_eq_probOutput,
    probEvent_map, probEvent_map]
  exact probEvent_mono'' fun r h => strongWin_of_weakWin r h

end SchemeBridge

/-- Every secure DAG scheme is weakly secure: a forgery on a new message is a strong forgery. -/
theorem Scheme.Secure.weaklySecure {P : Params} {S : Scheme P} (h : S.Secure) : S.WeaklySecure :=
  fun A B hB => lt_of_le_of_lt (SchemeBridge.weak_success_le S A)
    (h A B ((SchemeBridge.cost_iff S A B).2 hB))

end OptimalOTS
