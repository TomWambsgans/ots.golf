import Submissions.RiscvUpper.AlgorithmCosts

/-! Transfer an algorithm certificate to its canonical transmitted bit strings. -/

open OracleComp ENNReal
noncomputable section
open scoped Classical

namespace OptimalOTS.WireAdapter

variable {P : Params} (S : AlgorithmScheme P) (decode : List Bool → S.Signature)

abbrev scheme : AlgorithmScheme P where
  SecretKey := S.SecretKey
  Signature := List Bool
  encodeSignature := id
  encodeSignature_injective := Function.injective_id
  keygen := S.keygen
  sign := fun sk m => Option.map S.encodeSignature <$> S.sign sk m
  verify := fun pk m bits => S.verify pk m (decode bits)

def adversary (A : (scheme S decode).Adversary) : S.Adversary where
  State := A.State
  choose := A.choose
  forge := fun state signed =>
    (fun pair => (pair.1, decode pair.2)) <$> A.forge state (signed.map S.encodeSignature)

variable (inverse : ∀ σ, decode (S.encodeSignature σ) = σ)
  (canonical : ∀ pk m bits, true ∈ support (S.verify pk m (decode bits)) →
    S.encodeSignature (decode bits) = bits)

include inverse canonical in
theorem experiment_eq (A : (scheme S decode).Adversary) :
    (scheme S decode).experiment A = S.experiment (adversary S decode A) := by
  simp only [AlgorithmScheme.experiment, scheme, adversary, bind_map_left]
  apply bind_congr
  intro keys
  apply bind_congr
  intro chosen
  apply bind_congr
  intro signed
  apply bind_congr
  intro forged
  apply bind_congr_of_forall_mem_support
  intro ok hok
  cases ok with
  | false => rfl
  | true =>
    have hc := canonical keys.1 forged.1 forged.2 hok
    congr 1
    cases signed with
    | none => simp
    | some σ =>
      simp only [Option.map_some, Bool.true_and]
      have he : S.encodeSignature σ = forged.2 ↔ σ = decode forged.2 := by
        constructor
        · intro h
          have hd := congrArg decode h
          simpa only [inverse] using hd
        · intro h
          simpa only [h] using hc
      simp only [ne_eq, Option.some.injEq, Prod.mk.injEq, he]

include inverse canonical in
theorem secure (h : S.Secure) : (scheme S decode).Secure := by
  intro A B hB
  rw [experiment_eq S decode inverse canonical A] at hB ⊢
  exact h (adversary S decode A) B hB

include inverse in
theorem correct (h : S.Correct) : (scheme S decode).Correct := by
  unfold AlgorithmScheme.Correct at h ⊢
  intro message
  rw [← h message]
  congr 1
  simp only [scheme, bind_map_left]
  apply bind_congr
  intro keys
  apply bind_congr
  intro signed
  cases signed <;> simp only [Option.map_none, Option.map_some, inverse]

theorem signingFailure (ε : ℝ≥0∞) (h : S.SigningFailureAtMost ε) :
    (scheme S decode).SigningFailureAtMost ε := by
  intro message
  have original := h message
  simpa only [AlgorithmScheme.SigningFailureAtMost, scheme, bind_map_left,
    Option.isNone_map] using original

theorem signatureSize (n : ℕ) (h : S.SignatureSizeAtMost n) :
    (scheme S decode).SignatureSizeAtMost n := by
  intro sk m bits hb
  change some bits ∈ support (Option.map S.encodeSignature <$> S.sign sk m) at hb
  rw [support_map] at hb
  obtain ⟨signed, hs, he⟩ := hb
  cases signed with
  | none => cases he
  | some σ =>
    have equal : S.encodeSignature σ = bits := Option.some.inj he
    change bits.length ≤ n
    rw [← equal]
    exact h sk m σ hs

include canonical in
theorem rejectsOversized (n : ℕ) (h : S.RejectsOversized n) :
    (scheme S decode).RejectsOversized n := by
  intro pk m bits hsize accepted
  change n < bits.length at hsize
  have hc := canonical pk m bits accepted
  exact h pk m (decode bits) (by simpa only [hc] using hsize) accepted

include inverse canonical in
theorem admissible (L : AlgorithmScheme.Limits) (ε : ℝ≥0∞) (h : S.Admissible L ε) :
    (scheme S decode).Admissible L ε where
  failure_lt_one := h.failure_lt_one
  correct := correct S decode inverse h.correct
  signingFailure := signingFailure S decode ε h.signingFailure
  signatureSize := signatureSize S decode L.signatureBits h.signatureSize
  rejectsOversized := rejectsOversized S decode canonical L.signatureBits h.rejectsOversized
  keygenCost := h.keygenCost
  signCost := fun sk m => AlgorithmCosts.CostAtMost.map (h.signCost sk m) _

theorem verifyCost (c : ℕ) (h : S.VerifyCostAtMost c) : (scheme S decode).VerifyCostAtMost c :=
  fun pk m bits => h pk m (decode bits)

end OptimalOTS.WireAdapter
