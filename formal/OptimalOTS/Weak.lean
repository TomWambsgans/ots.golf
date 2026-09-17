import OptimalOTS.Statement

/-!
# Strong security implies weak security

`Scheme.Secure` asks that no accepted pair differ from the signer's; `Scheme.WeaklySecure` only
that no accepted pair carry a new message. The two experiments are the same run followed by two
winning conditions, and the weak condition implies the strong one, so the costs coincide and the
weak success probability is the smaller one: `Scheme.Secure.weaklySecure`.

The upper track certifies `Secure` schemes and the lower track bounds `WeaklySecure` ones, so this
theorem is what makes the two records bound the same number. It is not part of the contract: no
submission needs it, and none may import it.
-/

open OracleSpec OracleComp ENNReal

noncomputable section

open scoped Classical

namespace OptimalOTS

variable {P : Params}

/-- What a run of the forgery experiment produces, before anyone decides who won: the signed
message, the signature (`none` if signing failed), the attacker's pair, the verifier's verdict. -/
abbrev Outcome (P : Params) := Message P × Option (Signature P) × Message P × Signature P × Bool

/-- The run shared by `experiment` and `weakExperiment`. -/
def experimentRun (S : Scheme P) (A : Adversary P) : OracleComp (Spec P) (Outcome P) := do
  let (pk, sk) ← S.keygen
  let (m₁, st) ← A.choose pk
  let σ₁ ← S.sign sk m₁
  let (m₂, σ₂) ← A.forge st σ₁
  let ok ← S.verify pk m₂ σ₂
  return (m₁, σ₁, m₂, σ₂, ok)

/-- The winning condition of `experiment`. -/
def strongWin (r : Outcome P) : Bool :=
  r.2.2.2.2 && decide (r.2.1.map (fun s => (r.1, s)) ≠ some (r.2.2.1, r.2.2.2.1))

/-- The winning condition of `weakExperiment`. -/
def weakWin (r : Outcome P) : Bool :=
  r.2.2.2.2 && (r.2.1.isNone || decide (r.2.2.1 ≠ r.1))

theorem experiment_eq_map (S : Scheme P) (A : Adversary P) :
    experiment S A = strongWin <$> experimentRun S A := by
  simp only [experiment, experimentRun, strongWin, map_eq_bind_pure_comp, bind_assoc, pure_bind,
    Function.comp]

theorem weakExperiment_eq_map (S : Scheme P) (A : Adversary P) :
    weakExperiment S A = weakWin <$> experimentRun S A := by
  simp only [weakExperiment, experimentRun, weakWin, map_eq_bind_pure_comp, bind_assoc, pure_bind,
    Function.comp]

/-- A forgery on a new message is a forgery. -/
theorem strongWin_of_weakWin (r : Outcome P) (h : weakWin r = true) : strongWin r = true := by
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

theorem costAtMost_experiment_iff (S : Scheme P) (A : Adversary P) (B : ℕ) :
    CostAtMost P (experiment S A) B ↔ CostAtMost P (weakExperiment S A) B := by
  unfold CostAtMost
  rw [experiment_eq_map, weakExperiment_eq_map, isQueryBound_map_iff, isQueryBound_map_iff]

theorem probTrue_weakExperiment_le (S : Scheme P) (A : Adversary P) :
    probTrue P (weakExperiment S A) ≤ probTrue P (experiment S A) := by
  unfold probTrue
  rw [experiment_eq_map, weakExperiment_eq_map, simulateQ_map, simulateQ_map, StateT.run'_map',
    StateT.run'_map', ← probEvent_eq_eq_probOutput, ← probEvent_eq_eq_probOutput, probEvent_map,
    probEvent_map]
  exact probEvent_mono'' fun r h => strongWin_of_weakWin r h

/-- **Strong unforgeability implies existential unforgeability**, with the same bound. -/
theorem Scheme.Secure.weaklySecure {S : Scheme P} (h : S.Secure) : S.WeaklySecure := fun A B hB =>
  lt_of_le_of_lt (probTrue_weakExperiment_le S A) (h A B ((costAtMost_experiment_iff S A B).2 hB))

/-- A lower bound over weakly secure schemes is a lower bound over secure ones. -/
theorem VerificationLowerBound.of_secure {c : ℕ} (h : VerificationLowerBound P c) (S : Scheme P)
    (hS : S.Secure) : ∃ i : Fin P.numSets, c ≤ S.verifyCost i :=
  h S hS.weaklySecure

end OptimalOTS

/--
info: 'OptimalOTS.Scheme.Secure.weaklySecure' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms OptimalOTS.Scheme.Secure.weaklySecure
