import Submissions.RiscvUpper.Adapter

/-! Verification never uses private randomness: every query of `GScheme.verify` is a hash query. -/

open OracleSpec OracleComp

noncomputable section

open scoped Classical

namespace OptimalOTS

namespace Deterministic

variable {P : Params} {α β : Type}

theorem of_pure (x : α) : Deterministic P (pure x : OracleComp (Spec P) α) := trivial

theorem bind {oa : OracleComp (Spec P) α} {ob : α → OracleComp (Spec P) β}
    (h₁ : Deterministic P oa) (h₂ : ∀ x, Deterministic P (ob x)) :
    Deterministic P (oa >>= ob) := by
  induction oa using OracleComp.inductionOn with
  | pure x => simpa using h₂ x
  | query_bind t mx ih =>
    unfold Deterministic at h₁ ⊢
    rw [isQueryBound_query_bind_iff] at h₁
    rw [bind_assoc, isQueryBound_query_bind_iff]
    exact ⟨h₁.1, fun u => ih u (h₁.2 u)⟩

theorem map {oa : OracleComp (Spec P) α} (h : Deterministic P oa) (f : α → β) :
    Deterministic P (f <$> oa) :=
  (isQueryBound_map_iff oa f _ _ _).2 h

theorem hash {k : ℕ} (u : BitVec k) : Deterministic P (OptimalOTS.hash P u) := by
  unfold Deterministic OptimalOTS.hash
  rw [isQueryBound_query_iff]
  rfl

theorem foldlM {γ δ : Type} (f : γ → δ → OracleComp (Spec P) γ)
    (hf : ∀ x a, Deterministic P (f x a)) :
    ∀ (l : List δ) (init : γ), Deterministic P (l.foldlM f init)
  | [], _ => Deterministic.of_pure _
  | a :: l, init => by
      rw [List.foldlM_cons]
      exact Deterministic.bind (hf init a) fun y => Deterministic.foldlM f hf l y

end Deterministic

namespace Graph

variable {P : Params} (G : Graph P)

theorem deterministic_evalNode (x : G.Assignment) (v : Fin G.size)
    (s : OracleComp (Spec P) (BitVec (G.len v))) (hs : Deterministic P s) :
    Deterministic P (G.evalNode x v s) := by
  unfold Graph.evalNode
  cases G.kind v with
  | source => exact hs
  | det => exact Deterministic.of_pure _
  | hash p _ h => exact Deterministic.map (Deterministic.hash _) _

theorem deterministic_reconstruct (A : Finset (Fin G.size)) (given : G.Assignment) :
    Deterministic P (G.reconstruct A given) := by
  unfold Graph.reconstruct
  refine Deterministic.foldlM _ (fun x v => ?_) (List.finRange G.size) (fun _ => 0)
  split_ifs
  · exact Deterministic.of_pure _
  · exact Deterministic.map (G.deterministic_evalNode x v _ (Deterministic.of_pure _)) _
  · exact Deterministic.of_pure _

end Graph

namespace GScheme

variable {P : Params} (S : GScheme P)

theorem deterministic_verify (pk : PublicKey P) (m : Message P) (σ : Signature P) :
    Deterministic P (S.verify pk m σ) := by
  unfold GScheme.verify index
  refine Deterministic.bind (Deterministic.map (Deterministic.hash _) _) fun i => ?_
  split_ifs
  · dsimp only
    split_ifs
    · exact Deterministic.bind (S.graph.deterministic_reconstruct _ _)
        fun _ => Deterministic.of_pure _
    · exact Deterministic.of_pure _
  · exact Deterministic.of_pure _

/-- The adapter's verifier is deterministic. -/
theorem verifyDeterministic : S.toAlgorithm.VerifyDeterministic :=
  fun pk m σ => S.deterministic_verify pk m σ

end GScheme

end OptimalOTS
