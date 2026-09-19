import Submissions.RiscvUpper.AlgorithmCosts

/-! Honest-party resource bounds and wire-size bounds for the generic DAG adapter. -/

open OracleSpec OracleComp ENNReal
noncomputable section
open scoped Classical

namespace OptimalOTS.AlgorithmAdapter

variable {P : Params}

theorem length_encode (G : Graph P) (A : Finset (Fin G.size)) (x : G.Assignment) :
    (G.encode A x).length = G.revealBits A := by
  unfold Graph.encode Graph.revealBits
  rw [List.length_flatMap]
  simp only [toBits, List.length_ofFn]
  rw [← List.sum_toFinset _ ((List.nodup_finRange _).filter _)]
  congr 1
  ext v
  simp

theorem signLoop_returns (S : GScheme P) (x : S.graph.Assignment) (m : Message P) :
    ∀ k tried σ, some σ ∈ support (S.signLoop x m k tried) →
      ∃ i, σ.2 = S.graph.encode (S.sets i) x
  | 0, _, _, h => by simp [GScheme.signLoop] at h
  | k + 1, tried, σ, h => by
    rw [GScheme.signLoop] at h
    split_ifs at h with hf
    · rw [support_bind] at h
      simp only [Set.mem_iUnion] at h
      obtain ⟨j, _, h⟩ := h
      rw [support_bind] at h
      simp only [Set.mem_iUnion] at h
      obtain ⟨i, _, h⟩ := h
      split_ifs at h with hi
      · simp only [support_pure, Set.mem_singleton_iff, Option.some.injEq] at h
        exact ⟨⟨i, hi⟩, congrArg Prod.snd h⟩
      · exact signLoop_returns S x m k _ σ h
    · simp at h

theorem signatureSize (S : GScheme P) :
    S.toAlgorithm.SignatureSizeAtMost (P.nonceBits + P.maxRevealBits) := by
  change ∀ (sk : S.graph.Assignment) (m : Message P) (σ : Signature P),
    some σ ∈ support (S.sign sk m) → (encodeSignature σ).length ≤ P.nonceBits + P.maxRevealBits
  intro sk m σ hσ
  obtain ⟨i, hi⟩ := signLoop_returns S sk m P.trialLimit ∅ σ hσ
  rw [length_encodeSignature, hi, length_encode]
  exact Nat.add_le_add_left (S.reveal_le i) _

theorem rejectsOversized (S : GScheme P) :
    S.toAlgorithm.RejectsOversized (P.nonceBits + P.maxRevealBits) := by
  change ∀ (pk : PublicKey P) (m : Message P) (σ : Signature P),
    P.nonceBits + P.maxRevealBits < (encodeSignature σ).length →
      true ∉ support (S.verify pk m σ)
  intro pk m σ hlen hmem
  change P.nonceBits + P.maxRevealBits < (encodeSignature σ).length at hlen
  rw [length_encodeSignature] at hlen
  change true ∈ support (S.verify pk m σ) at hmem
  rw [GScheme.verify, support_bind] at hmem
  simp only [Set.mem_iUnion] at hmem
  obtain ⟨i, _, hmem⟩ := hmem
  by_cases hi : i ∈ validSet P
  · have hwrong : σ.2.length ≠ S.graph.revealBits (S.sets ⟨i, hi⟩) := by
      have h := S.reveal_le ⟨i, hi⟩
      omega
    simp only [dif_pos hi, if_neg hwrong, support_pure, Set.mem_singleton_iff] at hmem
    cases hmem
  · simp [hi] at hmem

theorem keygenCost (S : GScheme P) : S.toAlgorithm.KeygenCostAtMost P.keygenBudget :=
  AlgorithmCosts.GScheme.costAtMost_keygen S

theorem signCost (S : GScheme P) (hidx : blockCost P (P.msgBits + P.nonceBits) = 1) :
    S.toAlgorithm.SignCostAtMost P.trialLimit :=
  AlgorithmCosts.GScheme.costAtMost_sign S hidx

theorem verifyCost (S : GScheme P) (hidx : blockCost P (P.msgBits + P.nonceBits) = 1)
    {v : ℕ} (hv : ∀ i, S.graph.reconstructCost (S.sets i) ≤ v) :
    S.toAlgorithm.VerifyCostAtMost (1 + v) :=
  AlgorithmCosts.GScheme.costAtMost_verify S hidx hv

end OptimalOTS.AlgorithmAdapter
