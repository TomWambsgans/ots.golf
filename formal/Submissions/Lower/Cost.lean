import Submissions.Lower.Attack

/-!
# The cost of the attack experiment

With `q` construction attempts and `T` nonce trials, the whole experiment (key generation,
signing, the attack and final verification) costs at most `K + L c + T c + (q + 2) v + 2 c` on
every execution path, where `c = idxCost P` is the cost of an index query and `v` bounds the
reconstruction cost of every disclosure set.
-/

open OracleSpec OracleComp ENNReal

noncomputable section

open scoped Classical

namespace OptimalOTS

/-! ## Generic rules for `CostAtMost` -/

section Generic

variable {P : Params} {α β : Type}

theorem CostAtMost.mono {oa : OracleComp (Spec P) α} {b b' : ℕ} (h : CostAtMost P oa b)
    (hb : b ≤ b') : CostAtMost P oa b' := by
  induction oa using OracleComp.inductionOn generalizing b b' with
  | pure _ => trivial
  | query_bind t mx ih =>
      unfold CostAtMost at h ⊢
      rw [isQueryBound_query_bind_iff] at h ⊢
      exact ⟨le_trans h.1 hb, fun u => ih u (h.2 u) (by omega)⟩

theorem costAtMost_pure (x : α) (b : ℕ) : CostAtMost P (pure x : OracleComp (Spec P) α) b :=
  trivial

theorem CostAtMost.bind {oa : OracleComp (Spec P) α} {ob : α → OracleComp (Spec P) β}
    {b₁ b₂ : ℕ} (h₁ : CostAtMost P oa b₁) (h₂ : ∀ x, CostAtMost P (ob x) b₂) :
    CostAtMost P (oa >>= ob) (b₁ + b₂) :=
  isQueryBound_bind (· + ·)
    (fun _ _ _ _ h => ⟨le_add_left h, le_add_right h⟩)
    (fun _ _ _ _ h => ⟨by omega, by omega⟩) h₁ h₂

theorem costAtMost_map_iff (oa : OracleComp (Spec P) α) (f : α → β) (b : ℕ) :
    CostAtMost P (f <$> oa) b ↔ CostAtMost P oa b :=
  isQueryBound_map_iff _ _ _ _ _

theorem CostAtMost.map {oa : OracleComp (Spec P) α} {b : ℕ} (h : CostAtMost P oa b)
    (f : α → β) : CostAtMost P (f <$> oa) b :=
  (costAtMost_map_iff oa f b).2 h

theorem costAtMost_liftM_probComp (mx : ProbComp α) (b : ℕ) :
    CostAtMost P (liftM mx : OracleComp (Spec P) α) b := by
  change CostAtMost P (liftComp mx (Spec P)) b
  induction mx using OracleComp.inductionOn with
  | pure _ => trivial
  | query_bind t mx ih =>
      rw [liftComp_bind]
      have hq : liftComp (liftM (OracleSpec.query t) : ProbComp _) (Spec P) =
          (liftM ((Spec P).query (.inl t)) : OracleComp (Spec P) _) := by
        simp [liftComp]; rfl
      rw [hq]
      unfold CostAtMost at ih ⊢
      rw [isQueryBound_query_bind_iff]
      exact ⟨by simp [queryCost], fun u => by simpa [queryCost] using ih u⟩

theorem costAtMost_hash (τ : Label) {k : ℕ} (u : BitVec k) {b : ℕ} (hb : blockCost P k ≤ b) :
    CostAtMost P (hash P τ u) b := by
  unfold CostAtMost hash
  rw [isQueryBound_query_iff]
  exact hb


theorem CostAtMost.bind_le {oa : OracleComp (Spec P) α} {ob : α → OracleComp (Spec P) β}
    {b₁ b₂ b : ℕ} (h₁ : CostAtMost P oa b₁) (h₂ : ∀ x, CostAtMost P (ob x) b₂)
    (h : b₁ + b₂ ≤ b) : CostAtMost P (oa >>= ob) b :=
  (h₁.bind h₂).mono h

theorem costAtMost_foldlM {γ δ : Type} (f : γ → δ → OracleComp (Spec P) γ) (c : δ → ℕ)
    (hf : ∀ x a, CostAtMost P (f x a) (c a)) :
    ∀ (l : List δ) (init : γ), CostAtMost P (l.foldlM f init) (l.map c).sum
  | [], _ => costAtMost_pure _ _
  | a :: l, init => by
      rw [List.foldlM_cons, List.map_cons, List.sum_cons]
      exact (hf init a).bind fun y => costAtMost_foldlM f c hf l y

theorem sum_map_filter_finRange {n : ℕ} (p : Fin n → Prop) [DecidablePred p] (f : Fin n → ℕ) :
    (((List.finRange n).filter fun x => decide (p x)).map f).sum =
      ∑ x ∈ Finset.univ.filter p, f x := by
  rw [Finset.sum_filter, Fin.sum_univ_def]
  induction (List.finRange n) with
  | nil => simp
  | cons a l ih => by_cases h : p a <;> simp [h, ih]

end Generic

/-! ## Graph computations -/

namespace Graph

variable {P : Params} (G : Graph P)

theorem costAtMost_evalNode (x : G.Assignment) (v : Fin G.size)
    (s : OracleComp (Spec P) (BitVec (G.len v))) (hs : CostAtMost P s 0) :
    CostAtMost P (G.evalNode x v s) (G.nodeCost v) := by
  unfold Graph.evalNode Graph.nodeCost
  cases G.kind v with
  | source => exact hs
  | det => exact costAtMost_pure _ _
  | hash p _ τ h => exact (costAtMost_hash _ _ le_rfl).map _

theorem costAtMost_query (g : Fin G.size) (u : BitVec (G.kind g).inLen) :
    CostAtMost P ((G.kind g).query P u) (G.nodeCost g) := by
  unfold Graph.nodeCost
  revert u
  cases G.kind g with
  | source => intro u; exact costAtMost_pure _ _
  | det => intro u; exact costAtMost_pure _ _
  | hash p _ τ h => intro u; exact costAtMost_hash _ _ le_rfl

theorem costAtMost_sampleAssignment : CostAtMost P G.sampleAssignment 0 := by
  unfold Graph.sampleAssignment
  have := costAtMost_foldlM
    (fun (z : G.Assignment) v => Function.update z v <$> sampleBits P (G.len v)) (fun _ => 0)
    (fun _ _ => (costAtMost_liftM_probComp _ _).map _) (List.finRange G.size) (fun _ => 0)
  simpa using this

theorem costAtMost_evaluate (z : G.Assignment) : CostAtMost P (G.evaluate z) G.keygenCost := by
  unfold Graph.evaluate
  have := costAtMost_foldlM
    (fun (x : G.Assignment) v => Function.update x v <$> G.evalNode x v (pure (z v)))
    G.nodeCost (fun x v => (G.costAtMost_evalNode x v _ (costAtMost_pure _ _)).map _)
    (List.finRange G.size) (fun _ => 0)
  rwa [Graph.keygenCost, Fin.sum_univ_def]

theorem costAtMost_keygen : CostAtMost P G.keygen G.keygenCost :=
  G.costAtMost_sampleAssignment.bind_le (fun z => G.costAtMost_evaluate z) (by simp)

theorem costAtMost_reconstruct (A : Finset (Fin G.size)) (given : G.Assignment) :
    CostAtMost P (G.reconstruct A given) (G.reconstructCost A) := by
  unfold Graph.reconstruct
  refine CostAtMost.mono (costAtMost_foldlM _
    (fun v => if v ∈ A then 0 else if G.Visited A v then G.nodeCost v else 0)
    (fun x v => ?_) (List.finRange G.size) (fun _ => 0)) (le_of_eq ?_)
  · split_ifs
    · exact costAtMost_pure _ _
    · exact (G.costAtMost_evalNode x v _ (costAtMost_pure _ _)).map _
    · exact costAtMost_pure _ _
  · rw [← Fin.sum_univ_def, Graph.reconstructCost, Graph.evaluated, Finset.sum_filter]
    refine Finset.sum_congr rfl fun v _ => ?_
    by_cases h₁ : v ∈ A <;> by_cases h₂ : G.Visited A v <;> simp [h₁, h₂]

end Graph

/-! ## Signing and verification -/

theorem costAtMost_index {P : Params} (m : Message P) (η : Nonce P) :
    CostAtMost P (index P m η) (idxCost P) :=
  (costAtMost_hash _ _ le_rfl).map _

namespace Scheme

variable {P : Params} (S : Scheme P)

theorem costAtMost_keygen : CostAtMost P S.keygen P.keygenBudget :=
  (S.graph.costAtMost_keygen.bind_le (fun _ => costAtMost_pure _ 0) (by simp)).mono S.keygen_le

theorem costAtMost_signLoop (x : S.graph.Assignment) (m : Message P) :
    ∀ k tried, CostAtMost P (S.signLoop x m k tried) (k * idxCost P)
  | 0, _ => costAtMost_pure _ _
  | k + 1, tried => by
      rw [Scheme.signLoop]
      split_ifs
      · refine (costAtMost_liftM_probComp _ 0).bind_le (b₂ := (k + 1) * idxCost P) (fun j => ?_)
          (by simp)
        refine (costAtMost_index _ _).bind_le (b₂ := k * idxCost P) (fun i => ?_)
          (by rw [Nat.succ_mul]; omega)
        split_ifs with hi
        · exact costAtMost_pure _ _
        · exact costAtMost_signLoop x m k _
      · exact costAtMost_pure _ _

theorem costAtMost_sign (x : S.graph.Assignment) (m : Message P) :
    CostAtMost P (S.sign x m) (P.trialLimit * idxCost P) :=
  S.costAtMost_signLoop x m _ _

theorem costAtMost_verify {v : ℕ}
    (hv : ∀ i, S.graph.reconstructCost (S.sets i) ≤ v) (pk : PublicKey P) (m : Message P)
    (σ : Signature P) : CostAtMost P (S.verify pk m σ) (idxCost P + v) := by
  unfold Scheme.verify
  refine (costAtMost_index _ _).bind_le (b₂ := v) (fun i => ?_) le_rfl
  split_ifs with hi
  · dsimp only
    split_ifs
    · exact ((S.graph.costAtMost_reconstruct (S.sets ⟨i, hi⟩) _).mono (hv _)).bind_le
        (fun _ => costAtMost_pure _ 0) (by simp)
    · exact costAtMost_pure _ _
  · exact costAtMost_pure _ _

end Scheme

namespace Attack

variable {P : Params} (S : Scheme P)

theorem costAtMost_searchStep (i : Fin P.numSets) (C : Finset S.graph.Rec)
    (best : Option (ℕ × Fin P.numSets × Nonce P)) (k : ℕ) :
    CostAtMost P (searchStep S i C best k) (idxCost P) := by
  unfold searchStep
  refine (costAtMost_index _ _).bind_le (b₂ := 0) (fun j => ?_) (by simp)
  dsimp only
  split_ifs <;> exact costAtMost_pure _ _

theorem costAtMost_search (T : ℕ) (i : Fin P.numSets) (C : Finset S.graph.Rec) :
    CostAtMost P (search S T i C) (T * idxCost P) := by
  unfold search
  have := costAtMost_foldlM (searchStep S i C) (fun _ => idxCost P)
    (fun best k => costAtMost_searchStep S i C best k) (List.range T) none
  simpa [List.map_const', List.sum_replicate, smul_eq_mul] using this

theorem costAtMost_attemptM :
    ∀ (gs : List (Fin S.graph.size)) (C : Finset S.graph.Rec),
      CostAtMost P (attemptM S C gs) (gs.map S.graph.nodeCost).sum
  | [], C => costAtMost_pure _ _
  | g :: gs, C => by
      rw [attemptM]
      split_ifs with h
      · refine (costAtMost_liftM_probComp _ 0).bind_le
          (b₂ := S.graph.nodeCost g + (gs.map S.graph.nodeCost).sum) (fun k => ?_) (by simp)
        exact (S.graph.costAtMost_query g _).bind fun a => costAtMost_attemptM gs _
      · exact costAtMost_pure _ _

theorem costAtMost_attempts (C : Finset S.graph.Rec) (gs : List (Fin S.graph.size)) {w : ℕ}
    (hw : CostAtMost P (attemptM S C gs) w) : ∀ n, CostAtMost P (attempts S C gs n) (n * w)
  | 0 => costAtMost_pure _ _
  | n + 1 => by
      rw [attempts]
      refine hw.bind_le (b₂ := n * w) (fun r => ?_) (by rw [Nat.succ_mul, Nat.add_comm])
      rcases r with _ | ξ
      · exact costAtMost_attempts C gs hw n
      · exact costAtMost_pure _ _

theorem sum_newNodes_le (i j : Fin P.numSets) :
    ((newNodes S i j).map S.graph.nodeCost).sum ≤ S.graph.reconstructCost (S.sets j) := by
  unfold newNodes
  rw [sum_map_filter_finRange (fun g => g ∈ evalHashAt S j ∧ g ∉ evalHashAt S i)]
  refine Finset.sum_le_sum_of_subset fun g hg => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg
  exact (Finset.mem_filter.1 hg.1).1

theorem costAtMost_forge (q T : ℕ) {v : ℕ}
    (hv : ∀ i, S.graph.reconstructCost (S.sets i) ≤ v) :
    ∀ σ, CostAtMost P (forge S q T σ) (idxCost P + (v + (T * idxCost P + q * v)))
  | none => costAtMost_pure _ _
  | some (η₁, pl) => by
      simp only [forge]
      refine (costAtMost_index _ _).bind_le (b₂ := v + (T * idxCost P + q * v)) (fun i => ?_) le_rfl
      split_ifs with hi
      · refine ((S.graph.costAtMost_reconstruct (S.sets ⟨i, hi⟩) _).mono (hv _)).bind_le
          (b₂ := T * idxCost P + q * v) (fun xr => ?_) le_rfl
        refine (costAtMost_search S T _ _).bind_le (b₂ := q * v) (fun r => ?_) le_rfl
        rcases r with _ | ⟨_, j, η₂⟩
        · exact costAtMost_pure _ _
        · simp only
          split_ifs with hj
          · exact costAtMost_pure _ _
          · refine (costAtMost_attempts S _ _
              (((costAtMost_attemptM S (newNodes S ⟨i, hi⟩ j) _).mono
                (sum_newNodes_le S ⟨i, hi⟩ j)).mono (hv j)) q).bind_le
              (b₂ := 0) (fun r => ?_) (by simp)
            rcases r with _ | ξ
            · exact costAtMost_pure _ _
            · exact costAtMost_pure _ _
      · exact costAtMost_pure _ _


theorem costAtMost_experiment {P : Params} (S : Scheme P) (q T v : ℕ)
    (hv : ∀ i, S.graph.reconstructCost (S.sets i) ≤ v) :
    CostAtMost P (experiment S (adversary S q T))
      (P.keygenBudget + P.trialLimit * idxCost P + T * idxCost P + (q + 2) * v +
        2 * idxCost P) := by
  unfold experiment
  refine S.costAtMost_keygen.bind_le
    (b₂ := P.trialLimit * idxCost P +
      ((idxCost P + (v + (T * idxCost P + q * v))) + (idxCost P + v))) (fun x => ?_)
    (by nlinarith)
  rcases x with ⟨pk, sk⟩
  refine (costAtMost_pure _ 0).bind_le
    (b₂ := P.trialLimit * idxCost P +
      ((idxCost P + (v + (T * idxCost P + q * v))) + (idxCost P + v))) (fun y => ?_) (by simp)
  rcases y with ⟨m₁, st⟩
  refine (S.costAtMost_sign sk m₁).bind_le
    (b₂ := (idxCost P + (v + (T * idxCost P + q * v))) + (idxCost P + v)) (fun σ₁ => ?_) le_rfl
  refine (costAtMost_forge S q T hv σ₁).bind_le (b₂ := idxCost P + v) (fun z => ?_) le_rfl
  rcases z with ⟨m₂, σ₂⟩
  exact (S.costAtMost_verify hv pk m₂ σ₂).bind_le (fun _ => costAtMost_pure _ 0) (by simp)

end Attack

end OptimalOTS
