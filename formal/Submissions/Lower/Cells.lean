import Submissions.Lower.AnalysisDefs
import Submissions.Lower.Semantics

/-!
# The oracle cells of the attack experiment

Decoding queries to cells is injective, and every hash query of the attack experiment decodes.
-/

open OracleSpec OracleComp ENNReal

noncomputable section

open scoped Classical

namespace OptimalOTS

namespace Analysis

variable {P : Params} (S : Scheme P)

theorem bitVec_cast_heq {n m : ℕ} (h : n = m) (x : BitVec n) : HEq (x.cast h) x := by
  subst h; simp

theorem decode_injective :
    ∀ q q' c, decode S q = some c → decode S q' = some c → q = q' := by
  rintro ⟨_ | τ, ⟨k, u⟩⟩ ⟨_ | τ', ⟨k', u'⟩⟩ c h h'
  · simp only [decode] at h h'
    split_ifs at h h' with hk hk'
    subst hk hk'
    cases h
    simp only [Option.some.injEq, Sum.inr.injEq, BitVec.cast_eq] at h'
    rw [h']
  · simp only [decode] at h h'
    split_ifs at h h'
    cases h
    simp at h'
  · simp only [decode] at h h'
    split_ifs at h h'
    cases h
    simp at h'
  · simp only [decode] at h h'
    split_ifs at h h' with hh hh'
    cases h
    simp only [Option.some.injEq, Sum.inl.injEq] at h'
    obtain ⟨hv, hu⟩ := Sigma.mk.inj_iff.1 h'
    have hτ := (Classical.choose_spec hh').1
    have hk := (Classical.choose_spec hh').2
    rw [hv] at hτ hk
    rw [(Classical.choose_spec hh).1] at hτ
    rw [(Classical.choose_spec hh).2] at hk
    cases hτ
    subst hk
    have hu' : HEq u' u :=
      ((bitVec_cast_heq _ _).symm.trans hu).trans (bitVec_cast_heq _ _)
    cases eq_of_heq hu'
    rfl

section Helpers

variable {S}

theorem hq_pure {α : Type} (x : α) : HashQueriesIn (decode S) (pure x : OracleComp (Spec P) α) :=
  allQueriesSatisfy_pure _ _

theorem hq_bind {α β : Type} {oa : OracleComp (Spec P) α} {ob : α → OracleComp (Spec P) β}
    (h₁ : HashQueriesIn (decode S) oa) (h₂ : ∀ x, HashQueriesIn (decode S) (ob x)) :
    HashQueriesIn (decode S) (oa >>= ob) :=
  allQueriesSatisfy_bind h₁ h₂

theorem hq_map {α β : Type} {oa : OracleComp (Spec P) α} (f : α → β)
    (h : HashQueriesIn (decode S) oa) : HashQueriesIn (decode S) (f <$> oa) :=
  (isQueryBound_map_iff oa f () _ _).2 h

theorem hq_liftProb {α : Type} (pc : ProbComp α) :
    HashQueriesIn (decode S) (liftM pc : OracleComp (Spec P) α) := by
  rw [← OracleComp.liftComp_eq_liftM]
  induction pc using OracleComp.inductionOn with
  | pure x => exact hq_pure x
  | query_bind t k ih =>
    rw [OracleComp.liftComp_bind, OracleComp.liftComp_query]
    refine hq_bind (hq_map _ ?_) ih
    change AllQueriesSatisfy (liftM ((Spec P).query (Sum.inl t))) _
    rw [allQueriesSatisfy_query_iff]
    trivial

theorem hq_foldlM {α β : Type} (f : α → β → OracleComp (Spec P) α)
    (hf : ∀ a b, HashQueriesIn (decode S) (f a b)) (l : List β) (init : α) :
    HashQueriesIn (decode S) (l.foldlM f init) := by
  induction l generalizing init with
  | nil => exact hq_pure _
  | cons b l ih => exact hq_bind (hf init b) fun a => ih a

theorem decode_node_isSome (v : Fin S.graph.size) {p : Fin S.graph.size} {hp : p < v} {τ : ℕ}
    {hl : S.graph.len v = P.hashBits} (hk : S.graph.kind v = .hash p hp τ hl)
    (u : BitVec (S.graph.len p)) :
    (decode S (.node τ, ⟨S.graph.len p, u⟩)).isSome := by
  have hh : ∃ w, (S.graph.kind w).label? = some τ ∧ (S.graph.kind w).inLen = S.graph.len p :=
    ⟨v, by rw [hk]; rfl, by rw [hk]; rfl⟩
  simp only [decode, dif_pos hh, Option.isSome_some]

theorem hq_hash_node (v : Fin S.graph.size) {p : Fin S.graph.size} {hp : p < v} {τ : ℕ}
    {hl : S.graph.len v = P.hashBits} (hk : S.graph.kind v = .hash p hp τ hl)
    (u : BitVec (S.graph.len p)) :
    HashQueriesIn (decode S) (hash P (.node τ) u) := by
  unfold hash
  change AllQueriesSatisfy (liftM ((Spec P).query (Sum.inr _))) _
  rw [allQueriesSatisfy_query_iff]
  exact decode_node_isSome v hk u

theorem hq_index (m : Message P) (η : Nonce P) : HashQueriesIn (decode S) (index P m η) := by
  unfold index hash
  refine hq_map _ ?_
  change AllQueriesSatisfy (liftM ((Spec P).query (Sum.inr _))) _
  rw [allQueriesSatisfy_query_iff]
  simp [decode]

theorem hq_nodeQuery (g : Fin S.graph.size) (u : BitVec (S.graph.kind g).inLen) :
    HashQueriesIn (decode S) ((S.graph.kind g).query P u) := by
  have key : ∀ (k : NodeKind P.hashBits S.graph.size S.graph.len g), S.graph.kind g = k →
      ∀ u : BitVec k.inLen, HashQueriesIn (decode S) (k.query P u) := by
    intro k hk u
    cases k with
    | hash p hp τ hl => exact hq_hash_node g hk u
    | source => exact hq_pure _
    | det => exact hq_pure _
  exact key _ rfl u

theorem hq_evalNode (x : S.graph.Assignment) (v : Fin S.graph.size)
    (onSource : OracleComp (Spec P) (BitVec (S.graph.len v)))
    (hs : HashQueriesIn (decode S) onSource) :
    HashQueriesIn (decode S) (S.graph.evalNode x v onSource) := by
  unfold Graph.evalNode
  split
  · exact hs
  · exact hq_pure _
  · next p hp τ hl hk => exact hq_map _ (hq_hash_node v hk _)

theorem hq_reconstruct (A : Finset (Fin S.graph.size)) (given : S.graph.Assignment) :
    HashQueriesIn (decode S) (S.graph.reconstruct A given) := by
  unfold Graph.reconstruct
  refine hq_foldlM _ (fun x v => ?_) _ _
  split_ifs
  · exact hq_pure _
  · exact hq_map _ (hq_evalNode x v _ (hq_pure _))
  · exact hq_pure _

theorem hq_keygen : HashQueriesIn (decode S) S.keygen := by
  unfold Scheme.keygen Graph.keygen Graph.sampleAssignment Graph.evaluate
  refine hq_bind (hq_bind (hq_foldlM _ (fun z v => hq_map _ ?_) _ _) fun z =>
    hq_foldlM _ (fun x v => hq_map _ (hq_evalNode x v _ (hq_pure _))) _ _) fun x => hq_pure _
  exact hq_liftProb _

theorem hq_signLoop (x : S.graph.Assignment) (m : Message P) (k : ℕ) (tried : Finset (Nonce P)) :
    HashQueriesIn (decode S) (S.signLoop x m k tried) := by
  induction k generalizing tried with
  | zero => exact hq_pure _
  | succ k ih =>
    unfold Scheme.signLoop
    dsimp only
    split_ifs
    · refine hq_bind (hq_liftProb _) fun j => hq_bind (hq_index _ _) fun i => ?_
      split_ifs
      · exact hq_pure _
      · exact ih _
    · exact hq_pure _

theorem hq_verify (pk : PublicKey P) (m : Message P) (σ : Signature P) :
    HashQueriesIn (decode S) (S.verify pk m σ) := by
  unfold Scheme.verify
  refine hq_bind (hq_index _ _) fun i => ?_
  split_ifs
  · dsimp only
    split_ifs
    · exact hq_bind (hq_reconstruct _ _) fun _ => hq_pure _
    · exact hq_pure _
  · exact hq_pure _

theorem hq_search (T : ℕ) (i : Fin P.numSets) (C : Finset S.graph.Rec) :
    HashQueriesIn (decode S) (Attack.search S T i C) := by
  unfold Attack.search
  refine hq_foldlM _ (fun best k => ?_) _ _
  unfold Attack.searchStep
  refine hq_bind (hq_index _ _) fun j => ?_
  split_ifs
  · dsimp only
    split_ifs
    · exact hq_pure _
    · exact hq_pure _
  · exact hq_pure _

theorem hq_attemptM (gs : List (Fin S.graph.size)) (C : Finset S.graph.Rec) :
    HashQueriesIn (decode S) (Attack.attemptM S C gs) := by
  induction gs generalizing C with
  | nil => exact hq_pure _
  | cons g gs ih =>
    unfold Attack.attemptM
    split_ifs
    · exact hq_bind (hq_liftProb _) fun k => hq_bind (hq_nodeQuery g _) fun a => ih _
    · exact hq_pure _

theorem hq_attempts (C : Finset S.graph.Rec) (gs : List (Fin S.graph.size)) (n : ℕ) :
    HashQueriesIn (decode S) (Attack.attempts S C gs n) := by
  induction n with
  | zero => exact hq_pure _
  | succ n ih =>
    unfold Attack.attempts
    refine hq_bind (hq_attemptM gs C) fun r => ?_
    split
    · exact hq_pure _
    · exact ih

theorem hq_forge (q T : ℕ) (σ : Option (Signature P)) :
    HashQueriesIn (decode S) (Attack.forge S q T σ) := by
  rcases σ with _ | ⟨η₁, pl⟩
  · exact hq_pure _
  unfold Attack.forge
  refine hq_bind (hq_index _ _) fun i => ?_
  split_ifs
  · refine hq_bind (hq_reconstruct _ _) fun xr => hq_bind (hq_search _ _ _) fun r => ?_
    split
    · exact hq_pure _
    · split_ifs
      · exact hq_pure _
      · refine hq_bind (hq_attempts _ _ _) fun r' => ?_
        split
        · exact hq_pure _
        · exact hq_pure _
  · exact hq_pure _

end Helpers

theorem hashQueriesIn_experiment (q T : ℕ) :
    HashQueriesIn (decode S) (experiment S (Attack.adversary S q T)) := by
  unfold experiment
  refine hq_bind hq_keygen fun ⟨pk, sk⟩ => ?_
  refine hq_bind (hq_pure _) fun ⟨m₁, st⟩ => ?_
  refine hq_bind (hq_signLoop _ _ _ _) fun σ₁ => ?_
  refine hq_bind (hq_forge q T σ₁) fun ⟨m₂, σ₂⟩ => ?_
  exact hq_bind (hq_verify _ _ _) fun _ => hq_pure _

end Analysis

end OptimalOTS
