import OptimalOTS.Statement

/-!
# Strong security implies weak security

The strong and weak experiments make the same oracle calls and differ only in their winning
conditions. A weak win is a strong win: an accepted forgery must use a new message when signing
succeeds; after signing failure, any accepted pair wins in both experiments.

`Scheme.Secure.weaklySecure` (in `Statement.lean`) preserves the pathwise budget and security
bound, so the lower-bound attacks, which forge on a new message, apply to every secure scheme.
-/

open OracleSpec OracleComp ENNReal

noncomputable section

open scoped Classical

namespace OptimalOTS

variable {P : Params}

/-- The bridge itself, `Scheme.Secure.weaklySecure`, lives in `Statement.lean` so that the lower
roots can apply it; this file only re-exports the lower bound's consequence. -/
theorem VerificationLowerBound.of_secure {c : ℕ} (h : VerificationLowerBound P c) (S : Scheme P)
    (hS : S.Secure) : ∃ i : Fin P.numSets, c ≤ S.verifyCost i :=
  h S hS

end OptimalOTS

/--
info: 'OptimalOTS.Scheme.Secure.weaklySecure' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms OptimalOTS.Scheme.Secure.weaklySecure
