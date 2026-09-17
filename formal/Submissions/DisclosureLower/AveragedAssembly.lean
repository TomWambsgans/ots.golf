import Submissions.DisclosureLower.PatternAssembly
import Submissions.DisclosureLower.AveragedAttack
import Submissions.DisclosureLower.AveragedCounting
import Submissions.DisclosureLower.PatternGoods
import Submissions.DisclosureLower.PatternHelpers

/-! Average every reconstruction-pattern class to obtain a 33/1000 forgery probability. -/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal
noncomputable section
open scoped Classical
set_option linter.constructorNameAsVariable false

namespace OptimalOTS.AveragedAssembly
open PatternAttack

open BareLower

variable (S : Scheme paperParams)

attribute [local irreducible] signIdx signIdxLoop Scheme.sign Scheme.signLoop
  weakExperiment forge adversary Graph.encode Scheme.hashPattern Scheme.samePattern goodIndices

theorem signed_stage_ge (hcount : (Finset.univ.image S.hashPattern).card ≤ Nat.choose 123 46)
    (x : S.graph.Assignment) (c : Cache paperParams) (hc : S.graph.CacheConsistent x c)
    (D : Finset Query) (hD : HasSupport c D) (hcard : D.card ≤ 1024)
    (m : Message paperParams) (hfresh : FreshMessage c m) :
    (11 / 300 : ℝ≥0∞) ≤ E (run paperParams (signIdx paperParams m) c)
      (fun p => E (run paperParams (afterSign S (2 ^ 122) (S.publicKey x) x m p.1) p.2) win) := by
  let f := fun i : Fin paperParams.numSets => AveragedSearch.hitRate (S.samePattern i).card
  have hsign : (11 / 270 : ℝ≥0∞) ≤
      E (run paperParams (signIdx paperParams m) c) (fun p => AveragedSigning.reward f p.1) := by
    rw [AveragedSigning.sign_reward_eq f m c hfresh]
    exact AveragedCounting.paper_weighted_rate_ge S hcount
  have hstage : E (run paperParams (signIdx paperParams m) c)
      (fun p => AveragedSigning.reward f p.1) * (9 / 10) ≤
      E (run paperParams (signIdx paperParams m) c)
        (fun p => E (run paperParams (afterSign S (2 ^ 122) (S.publicKey x) x m p.1) p.2) win) := by
    rw [← expectedValue_mul_const]
    apply expectedValue_mono_of_support
    intro p hp
    obtain ⟨hsub, _, hidx⟩ := signIdx_support paperParams m c p hp
    obtain ⟨D', hD', hcard'⟩ := exists_support_run (signIdx paperParams m)
      (cost_signIdx S (by decide) m) hD p hp
    have hcard'' : D'.card ≤ 2 ^ 22 := by
      change D'.card ≤ D.card + 2 ^ 21 at hcard'
      omega
    cases hr : p.1 with
    | none => simp only [AveragedSigning.reward, zero_mul, zero_le]
    | some r =>
      obtain ⟨η,i⟩ := r
      simp only [AveragedSigning.reward, afterSign_some]
      obtain ⟨w, hw, hwi⟩ := hidx η i hr
      simpa only [f, mul_comm] using
        AveragedAttack.forge_success_ge S i x p.2 (Graph.CacheConsistent.mono _ hsub hc)
          D' hD' hcard'' m η w hw hwi
  calc
    (11 / 300 : ℝ≥0∞) = (11 / 270) * (9 / 10) := by
      apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
      norm_num [ENNReal.toReal_div]
    _ ≤ _ := (mul_le_mul' hsign le_rfl).trans hstage

theorem choose_stage_ge (hcount : (Finset.univ.image S.hashPattern).card ≤ Nat.choose 123 46)
    (x : S.graph.Assignment) (c : Cache paperParams) (hc : S.graph.CacheConsistent x c)
    (D : Finset Query) (hD : HasSupport c D) (hcard : D.card ≤ 1024) :
    (33 / 1000 : ℝ≥0∞) ≤ E ($ᵗ BitVec paperParams.msgBits) (fun m =>
      E (run paperParams (signIdx paperParams m) c)
        (fun p => E (run paperParams (afterSign S (2 ^ 122) (S.publicKey x) x m p.1) p.2) win)) := by
  have hmass := fresh_mass_paper hD (hcard.trans (by norm_num : 1024 ≤ 2 ^ 22))
  have h := expectedValue_ge_indicator ($ᵗ BitVec paperParams.msgBits) (FreshMessage c)
    (fun m => E (run paperParams (signIdx paperParams m) c)
      (fun p => E (run paperParams (afterSign S (2 ^ 122) (S.publicKey x) x m p.1) p.2) win))
    (11 / 300) (fun m _ hm => signed_stage_ge S hcount x c hc D hD hcard m hm)
  calc
    (33 / 1000 : ℝ≥0∞) = (9 / 10) * (11 / 300) := by
      apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
      norm_num [ENNReal.toReal_div]
    _ ≤ _ := (mul_le_mul' hmass le_rfl).trans h

theorem success_ge_count (hcount : (Finset.univ.image S.hashPattern).card ≤ Nat.choose 123 46) :
    (33 / 1000 : ℝ≥0∞) ≤ probTrue paperParams (weakExperiment S (adversary S (2 ^ 122))) := by
  rw [probTrue_eq_expectation, experiment_eq, run_bind, E_bind]
  rw [← expectedValue_const (mx := run paperParams S.keygen ∅) (by simp)
    (33 / 1000 : ℝ≥0∞)]
  apply expectedValue_mono_of_support
  intro p hp
  obtain ⟨hpk, hc⟩ := S.keygen_cacheConsistent ∅ p hp
  obtain ⟨D, hD, hcard⟩ := exists_support_run_empty S.costAtMost_keygen p hp
  change D.card ≤ 1024 at hcard
  rcases p with ⟨⟨pk,x⟩,c⟩
  dsimp only at hpk hc hD hcard ⊢
  subst hpk
  rw [run_bind, E_bind, sampleBits, run_liftM, E_map]
  simp only [run_bind, E_bind]
  exact choose_stage_ge S hcount x c hc D hD hcard

/-- The whole experiment, including key generation and signing, beats 127-bit security. -/
theorem budget_lt :
    ((paperParams.keygenBudget + paperParams.trialLimit + 2 ^ 122 + 2 * 78 + 2 : ℕ) : ℝ≥0∞) /
      2 ^ paperParams.securityBits < 33 / 1000 := by
  apply (ENNReal.toReal_lt_toReal (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_div, paperParams]

end OptimalOTS.AveragedAssembly
