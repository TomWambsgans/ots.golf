import Submissions.Lower.AnalysisDefs
import Submissions.Lower.Semantics
import Submissions.Lower.Ranks

/-!
# Unrolling the attack experiment with a fixed table

With a fixed oracle table, the probability that the attack experiment succeeds is at least an
explicit sum over the sources, the signed index and the rank found by the nonce search.

The proof computes each component of the experiment with a fixed table (`Decomp.sim_evaluate`,
`Decomp.sim_reconstruct`, `Decomp.sim_signLoop`, `Decomp.sim_search`, `Decomp.probEvent_attempts`,
`Decomp.probOutput_sampleAssignment`), shows that the forgery verifies (`Decomp.cands_eq`,
`Decomp.forged_nodeEqs`, `Decomp.sim_verify_true`), and assembles the bound
(`Decomp.forge_stage`).
-/

open OracleSpec OracleComp ENNReal

noncomputable section

open scoped Classical

namespace OptimalOTS

namespace Analysis

open Attack

variable {P : Params} (S : Scheme P)

namespace Decomp

variable (g : Cell S → BitVec P.hashBits)

theorem sim_liftProb {α : Type} (pc : ProbComp α) :
    simulateQ (tableImpl P (decode S) g) (liftM pc : OracleComp (Spec P) α) = pc := by
  simp [tableImpl, QueryImpl.simulateQ_add_liftM_left, QueryImpl.simulateQ_toQueryImpl]

theorem setWidth_append_nonce' (m : Message P) (η : Nonce P) :
    (m ++ η).setWidth P.nonceBits = η := by
  ext j hj
  simp [BitVec.getElem_setWidth, BitVec.getLsbD_append, hj]

theorem sim_index (m : Message P) (η : Nonce P) :
    simulateQ (tableImpl P (decode S) g) (index P m η) =
      pure (idxOfOut P (nonceTab S g m η)) := by
  simp [index, hash, tableImpl, idxOfOut, nonceTab, decode]

theorem signImpl_index (u : Nonce P → BitVec P.hashBits) (m : Message P) (η : Nonce P) :
    simulateQ (signImpl P u) (index P m η) = pure (idxOfOut P (u η)) := by
  simp [index, hash, signImpl, idxOfOut, setWidth_append_nonce']

theorem bitVec_cast_heq' {n m : ℕ} (h : n = m) (x : BitVec n) : HEq (x.cast h) x := by
  subst h; simp

theorem bitVec_cast_heq_cast {n m k : ℕ} (h : n = m) (h' : n = k) (x : BitVec n) :
    HEq (x.cast h) (x.cast h') := by
  subst h h'; rfl

theorem decode_node (v : Fin S.graph.size) {p : Fin S.graph.size} {hp : p < v} {τ : ℕ}
    {hl : S.graph.len v = P.hashBits} (hk : S.graph.kind v = .hash p hp τ hl)
    (u : BitVec (S.graph.len p)) :
    decode S (.node τ, ⟨S.graph.len p, u⟩) = some (.inl ⟨v, u.cast (by rw [hk]; rfl)⟩) := by
  have hh : ∃ w, (S.graph.kind w).label? = some τ ∧ (S.graph.kind w).inLen = S.graph.len p :=
    ⟨v, by rw [hk]; rfl, by rw [hk]; rfl⟩
  have hv : Classical.choose hh = v :=
    S.graph.label_injective _ _ τ (Classical.choose_spec hh).1 (by rw [hk]; rfl)
  simp only [decode, dif_pos hh, Option.some.injEq, Sum.inl.injEq]
  refine Sigma.ext hv ?_
  dsimp only
  apply bitVec_cast_heq_cast

theorem sim_hash_node (v : Fin S.graph.size) {p : Fin S.graph.size} {hp : p < v} {τ : ℕ}
    {hl : S.graph.len v = P.hashBits} (hk : S.graph.kind v = .hash p hp τ hl)
    (u : BitVec (S.graph.len p)) :
    simulateQ (tableImpl P (decode S) g) (hash P (.node τ) u) =
      pure (g (.inl ⟨v, u.cast (by rw [hk]; rfl)⟩)) := by
  simp [hash, tableImpl, decode_node S v hk u]

theorem input_heq_of_hash (v : Fin S.graph.size) {p : Fin S.graph.size} {hp : p < v} {τ : ℕ}
    {hl : S.graph.len v = P.hashBits} (hk : S.graph.kind v = .hash p hp τ hl)
    (x : S.graph.Assignment) : HEq ((S.graph.kind v).input x) (x p) := by
  rw [hk]; rfl

theorem sim_evalNode (x : S.graph.Assignment) (v : Fin S.graph.size) (s : BitVec (S.graph.len v)) :
    simulateQ (tableImpl P (decode S) g) (S.graph.evalNode x v (pure s)) =
      pure ((S.graph.kind v).value x s (graphTab S g v ((S.graph.kind v).input x))) := by
  unfold Graph.evalNode
  split
  · next hk =>
    simp only [simulateQ_pure, graphTab]
    generalize g (Sum.inl ⟨v, (S.graph.kind v).input x⟩) = a
    rw [hk]; rfl
  · next ps hps f hf hk =>
    simp only [simulateQ_pure, graphTab]
    generalize g (Sum.inl ⟨v, (S.graph.kind v).input x⟩) = a
    rw [hk]; rfl
  · next p hp τ hl hk =>
    rw [simulateQ_map, sim_hash_node S g v hk]
    have hc : (⟨v, (x p).cast (by rw [hk]; rfl)⟩ : Σ w : Fin S.graph.size, BitVec (S.graph.kind w).inLen) =
        ⟨v, (S.graph.kind v).input x⟩ :=
      Sigma.ext rfl (by
        dsimp only
        exact HEq.trans (bitVec_cast_heq' _ (x p)) (input_heq_of_hash S v hk x).symm)
    rw [hc]
    simp only [map_pure, graphTab]
    generalize g (Sum.inl ⟨v, (S.graph.kind v).input x⟩) = a
    rw [hk]; rfl

theorem sim_foldlM_pure {α β : Type} (f : α → β → OracleComp (Spec P) α) (F : α → β → α)
    (hf : ∀ a b, simulateQ (tableImpl P (decode S) g) (f a b) = pure (F a b)) (l : List β) (init : α) :
    simulateQ (tableImpl P (decode S) g) (l.foldlM f init) = pure (l.foldl F init) := by
  induction l generalizing init with
  | nil => simp
  | cons b l ih => simp [List.foldlM_cons, hf, ih]

theorem sim_evaluate (z : S.graph.Assignment) :
    simulateQ (tableImpl P (decode S) g) (S.graph.evaluate z) =
      pure (S.graph.evalTab z (graphTab S g)) := by
  unfold Graph.evaluate Graph.evalTab Graph.evalWith
  refine sim_foldlM_pure S g _ _ (fun x v => ?_) _ _
  rw [simulateQ_map, sim_evalNode]
  rfl

theorem sim_reconstruct (A : Finset (Fin S.graph.size)) (given : S.graph.Assignment) :
    simulateQ (tableImpl P (decode S) g) (S.graph.reconstruct A given) =
      pure (S.graph.reconTab (graphTab S g) A given) := by
  unfold Graph.reconstruct Graph.reconTab Graph.evalWith
  refine sim_foldlM_pure S g _ _ (fun x v => ?_) _ _
  by_cases h1 : v ∈ A
  · simp [h1, Graph.reconVal]
  · by_cases h2 : S.graph.Visited A v
    · simp only [h1, h2, if_false, if_true, simulateQ_map, sim_evalNode, map_pure, Graph.reconVal]
    · simp [h1, h2, Graph.reconVal]

theorem signImpl_liftProb (u : Nonce P → BitVec P.hashBits) {α : Type} (pc : ProbComp α) :
    simulateQ (signImpl P u) (liftM pc : OracleComp (Spec P) α) = pc := by
  simp [signImpl, QueryImpl.simulateQ_add_liftM_left, QueryImpl.simulateQ_toQueryImpl]

theorem sim_signLoop (x : S.graph.Assignment) (k : ℕ) (tried : Finset (Nonce P)) :
    simulateQ (tableImpl P (decode S) g) (S.signLoop x (msg₁ P) k tried) =
      simulateQ (signImpl P (nonceTab S g (msg₁ P))) (S.signLoop x (msg₁ P) k tried) := by
  induction k generalizing tried with
  | zero => simp [Scheme.signLoop]
  | succ k ih =>
    unfold Scheme.signLoop
    dsimp only
    split_ifs with h
    · simp only [simulateQ_bind, sim_liftProb, signImpl_liftProb, sim_index, signImpl_index,
        pure_bind]
      refine bind_congr fun j => ?_
      split_ifs
      · simp
      · exact ih _
    · rfl

theorem probOutput_foldl_sample (l : List (Fin S.graph.size)) (hl : l.Nodup)
    (init z : S.graph.Assignment) :
    Pr[= z | simulateQ (tableImpl P (decode S) g) (l.foldlM
      (fun z v => Function.update z v <$> sampleBits P (S.graph.len v)) init)] =
      if ∀ v, v ∉ l → z v = init v then
        (l.map fun v => (Fintype.card (BitVec (S.graph.len v)) : ℝ≥0∞)⁻¹).prod else 0 := by
  induction l generalizing init with
  | nil =>
    simp only [List.foldlM_nil, simulateQ_pure, probOutput_pure, List.not_mem_nil,
      not_false_eq_true, forall_const, List.map_nil, List.prod_nil]
    by_cases h : z = init
    · subst h; simp
    · rw [if_neg h, if_neg (fun h' => h (funext h'))]
  | cons v l ih =>
    rw [List.nodup_cons] at hl
    rw [List.foldlM_cons, simulateQ_bind, simulateQ_map, sampleBits, sim_liftProb,
      map_eq_bind_pure_comp, bind_assoc, probOutput_bind_eq_sum_fintype]
    simp only [pure_bind, Function.comp, probOutput_uniformSample, ih hl.2]
    rw [Finset.sum_eq_single (z v)]
    · by_cases hc : ∀ w, w ∉ v :: l → z w = init w
      · rw [if_pos, if_pos hc, List.map_cons, List.prod_cons]
        intro w hw
        by_cases hwv : w = v
        · subst hwv; simp
        · rw [Function.update_of_ne hwv]
          exact hc w (by simp [hwv, hw])
      · rw [if_neg, if_neg hc, mul_zero]
        intro h'
        apply hc
        intro w hw
        simp only [List.mem_cons, not_or] at hw
        have := h' w hw.2
        rwa [Function.update_of_ne hw.1] at this
    · intro b _ hb
      rw [if_neg, mul_zero]
      intro h'
      have := h' v hl.1
      rw [Function.update_self] at this
      exact hb this.symm
    · simp

/-! ## Nonce search -/

/-- One nonce trial with a nonce table, as a pure function. -/
def stepPure (i : Fin P.numSets) (C : Finset S.graph.Rec) (w : Nonce P → BitVec P.hashBits)
    (best : Option (ℕ × Fin P.numSets × Nonce P)) (k : ℕ) :
    Option (ℕ × Fin P.numSets × Nonce P) :=
  if hj : idxOfOut P (w (BitVec.ofNat P.nonceBits k)) < P.numSets then
    if rank S i C ⟨_, hj⟩ < 100 ∧ ∀ b ∈ best, rank S i C ⟨_, hj⟩ < b.1 then
      some (rank S i C ⟨_, hj⟩, ⟨_, hj⟩, BitVec.ofNat P.nonceBits k)
    else best
  else best

theorem sim_search (T : ℕ) (i : Fin P.numSets) (C : Finset S.graph.Rec) :
    simulateQ (tableImpl P (decode S) g) (search S T i C) =
      pure ((List.range T).foldl (stepPure S i C (nonceTab S g (msg₂ P))) none) := by
  unfold search
  refine sim_foldlM_pure S g _ _ (fun best k => ?_) _ _
  unfold searchStep stepPure
  simp only [simulateQ_bind, sim_index, pure_bind]
  split_ifs <;> simp

/-- Validity of a search state. -/
def SValid (i : Fin P.numSets) (C : Finset S.graph.Rec) (w : Nonce P → BitVec P.hashBits)
    (best : Option (ℕ × Fin P.numSets × Nonce P)) : Prop :=
  ∀ r j η, best = some (r, j, η) → rank S i C j = r ∧ idxOfOut P (w η) = j.val

theorem stepPure_valid (i : Fin P.numSets) (C : Finset S.graph.Rec)
    (w : Nonce P → BitVec P.hashBits) (best : Option (ℕ × Fin P.numSets × Nonce P)) (k : ℕ)
    (hb : SValid S i C w best) : SValid S i C w (stepPure S i C w best k) := by
  unfold stepPure
  split_ifs with h1 h2
  · intro r j η h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨rfl, rfl⟩
  · exact hb
  · exact hb

theorem min?_cons_cons (a b : ℕ) (L : List ℕ) : (a :: b :: L).min? = (min a b :: L).min? := rfl

theorem foldl_stepPure_map (i : Fin P.numSets) (C : Finset S.graph.Rec)
    (w : Nonce P → BitVec P.hashBits) (l : List ℕ) (best : Option (ℕ × Fin P.numSets × Nonce P)) :
    (l.foldl (stepPure S i C w) best).map Prod.fst =
      ((best.map Prod.fst).toList ++
        l.filterMap fun k => rkOf S i C (idxOfOut P (w (BitVec.ofNat P.nonceBits k)))).min? := by
  induction l generalizing best with
  | nil => rcases best with _ | ⟨r, j, η⟩ <;> simp
  | cons k l ih =>
    rw [List.foldl_cons, ih, List.filterMap_cons]
    by_cases h1 : idxOfOut P (w (BitVec.ofNat P.nonceBits k)) < P.numSets
    · by_cases h3 : rank S i C ⟨_, h1⟩ < 100
      · have hF : rkOf S i C (idxOfOut P (w (BitVec.ofNat P.nonceBits k))) =
            some (rank S i C ⟨_, h1⟩) := by
          simp only [rkOf, dif_pos h1, if_pos h3]
        simp only [hF]
        rcases best with _ | ⟨b, jb, ηb⟩
        · simp only [stepPure, dif_pos h1]
          rw [if_pos ⟨h3, by simp⟩]
          simp
        · by_cases h4 : rank S i C ⟨_, h1⟩ < b
          · simp only [stepPure, dif_pos h1]
            rw [if_pos ⟨h3, by simpa using h4⟩]
            simp only [Option.map_some, Option.toList_some, List.cons_append, List.nil_append]
            rw [min?_cons_cons, min_eq_right h4.le]
          · simp only [stepPure, dif_pos h1]
            rw [if_neg (by simp [h4])]
            simp only [Option.map_some, Option.toList_some, List.cons_append, List.nil_append]
            rw [min?_cons_cons, min_eq_left (not_lt.1 h4)]
      · have hF : rkOf S i C (idxOfOut P (w (BitVec.ofNat P.nonceBits k))) = none := by
          simp only [rkOf, dif_pos h1, if_neg h3]
        simp only [hF, stepPure, dif_pos h1]
        rw [if_neg (by simp [h3])]
    · have hF : rkOf S i C (idxOfOut P (w (BitVec.ofNat P.nonceBits k))) = none := by
        simp only [rkOf, dif_neg h1]
      simp only [hF, stepPure, dif_neg h1]

theorem search_spec (T : ℕ) (i : Fin P.numSets) (C : Finset S.graph.Rec)
    (w : Nonce P → BitVec P.hashBits) {ℓ : ℕ} (h : bestPure P T (rkOf S i C) w = some ℓ) :
    ∃ j η, (List.range T).foldl (stepPure S i C w) none = some (ℓ, j, η) ∧
      rank S i C j = ℓ ∧ idxOfOut P (w η) = j.val := by
  have hm := foldl_stepPure_map S i C w (List.range T) none
  simp only [Option.map_none, Option.toList_none, List.nil_append] at hm
  unfold bestPure at h
  rw [h] at hm
  have hv : SValid S i C w ((List.range T).foldl (stepPure S i C w) none) := by
    generalize (List.range T) = l
    have : ∀ best, SValid S i C w best → SValid S i C w (l.foldl (stepPure S i C w) best) := by
      induction l with
      | nil => exact fun _ hb => hb
      | cons k l ih => exact fun best hb => ih _ (stepPure_valid S i C w best k hb)
    exact this none (by intro r j η h; cases h)
  rcases hr : (List.range T).foldl (stepPure S i C w) none with _ | ⟨r, j, η⟩
  · rw [hr] at hm; cases hm
  · rw [hr] at hm hv
    simp only [Option.map_some, Option.some.injEq] at hm
    subst hm
    exact ⟨j, η, rfl, hv r j η rfl⟩

/-! ## Construction attempts -/

theorem sim_nodeQuery_aux (v : Fin S.graph.size) :
    ∀ (k : NodeKind P.hashBits S.graph.size S.graph.len v) (_hk : S.graph.kind v = k)
      (u : BitVec k.inLen) (u' : BitVec (S.graph.kind v).inLen), HEq u u' → k.IsHash →
      simulateQ (tableImpl P (decode S) g) (k.query P u) = pure (g (.inl ⟨v, u'⟩)) := by
  intro k hk u u' hu hh
  cases k with
  | hash p hp τ hl =>
    refine (sim_hash_node S g v hk u).trans
      (congrArg (fun c => (pure (g (Sum.inl c)) : ProbComp (BitVec P.hashBits))) (Sigma.ext rfl ?_))
    exact HEq.trans (bitVec_cast_heq' (by rw [hk]) u) hu
  | source => exact absurd hh id
  | det => exact absurd hh id

theorem sim_nodeQuery (v : Fin S.graph.size) (hv : (S.graph.kind v).IsHash)
    (u : BitVec (S.graph.kind v).inLen) :
    simulateQ (tableImpl P (decode S) g) ((S.graph.kind v).query P u) = pure (graphTab S g v u) :=
  sim_nodeQuery_aux S g v _ rfl u u HEq.rfl hv

theorem sum_fin_equivFin' {α : Type*} {s : Finset α} {n : ℕ} (h : n = s.card) (G : α → ℝ≥0∞) :
    ∑ j : Fin n, G (s.equivFin.symm (Fin.cast h j)).1 = ∑ η ∈ s, G η := by
  rw [← Finset.sum_coe_sort s]
  exact Equiv.sum_comp ((finCongr h).trans s.equivFin.symm) (fun x => G x.1)

theorem attemptProbNodes_mem (t : S.graph.Tab) (gs : List (Fin S.graph.size)) (W : Finset S.graph.Rec) :
    0 ≤ attemptProbNodes S t gs W ∧ attemptProbNodes S t gs W ≤ 1 := by
  induction gs generalizing W with
  | nil => unfold attemptProbNodes; split_ifs <;> norm_num
  | cons v gs ih =>
    unfold attemptProbNodes
    split_ifs with hW
    · have hc : (0 : ℝ) < W.card := by exact_mod_cast Finset.card_pos.mpr hW
      constructor
      · exact div_nonneg (Finset.sum_nonneg fun _ _ => (ih _).1) hc.le
      · rw [div_le_one hc]
        calc _ ≤ ∑ _ξ ∈ W, (1 : ℝ) := Finset.sum_le_sum fun _ _ => (ih _).2
          _ = W.card := by simp
    · norm_num

/-- The step of an attempt, in terms of the working sets. -/
theorem probEvent_attemptM_cons (v : Fin S.graph.size) (hv : (S.graph.kind v).IsHash)
    (gs : List (Fin S.graph.size)) (C : Finset S.graph.Rec) (hC : 0 < C.card)
    (Φ : Option S.graph.Rec → Prop) :
    Pr[Φ | simulateQ (tableImpl P (decode S) g) (attemptM S C (v :: gs))] =
      ∑ ξ ∈ C, (C.card : ℝ≥0∞)⁻¹ * Pr[Φ | simulateQ (tableImpl P (decode S) g) (attemptM S
        (C.filter fun ξ' => (S.graph.kind v).input (S.graph.evalRec ξ') =
            (S.graph.kind v).input (S.graph.evalRec ξ) ∧
          ξ'.2 v = graphTab S g v ((S.graph.kind v).input (S.graph.evalRec ξ))) gs)] := by
  rw [attemptM, dif_pos hC]
  simp only [simulateQ_bind, sim_liftProb, sim_nodeQuery S g v hv, pure_bind]
  rw [probEvent_bind_eq_sum_fintype]
  simp only [ProbComp.probOutput_uniformFin]
  have hc' : C.card - 1 + 1 = C.card := by omega
  have hc : ((C.card - 1 : ℕ) : ℝ≥0∞) + 1 = C.card := by exact_mod_cast hc'
  rw [hc]
  exact sum_fin_equivFin' (by omega) (fun ξ => (C.card : ℝ≥0∞)⁻¹ * Pr[Φ | simulateQ
    (tableImpl P (decode S) g) (attemptM S (C.filter fun ξ' => (S.graph.kind v).input
      (S.graph.evalRec ξ') = (S.graph.kind v).input (S.graph.evalRec ξ) ∧
        ξ'.2 v = graphTab S g v ((S.graph.kind v).input (S.graph.evalRec ξ))) gs)])

theorem probOutput_attemptM_none (gs : List (Fin S.graph.size))
    (hgs : ∀ v ∈ gs, (S.graph.kind v).IsHash) (C : Finset S.graph.Rec) :
    Pr[= none | simulateQ (tableImpl P (decode S) g) (attemptM S C gs)] =
      ENNReal.ofReal (1 - attemptProbNodes S (graphTab S g) gs C) := by
  induction gs generalizing C with
  | nil =>
    unfold attemptM attemptProbNodes
    by_cases hC : C.Nonempty <;> simp [hC]
  | cons v gs ih =>
    by_cases hC : 0 < C.card
    · have hW : C.Nonempty := Finset.card_pos.mp hC
      rw [← probEvent_eq_eq_probOutput, probEvent_attemptM_cons S g v (hgs v (by simp)) gs C hC]
      simp only [probEvent_eq_eq_probOutput, ih (fun w hw => hgs w (by simp [hw]))]
      rw [attemptProbNodes.eq_2, if_pos hW]
      have hcR : (0 : ℝ) < C.card := by exact_mod_cast hC
      rw [← Finset.mul_sum, ← ENNReal.ofReal_sum_of_nonneg (fun ξ _ => sub_nonneg.2
        (attemptProbNodes_mem S _ _ _).2)]
      rw [show ((C.card : ℝ≥0∞))⁻¹ = ENNReal.ofReal ((C.card : ℝ))⁻¹ by
        rw [ENNReal.ofReal_inv_of_pos hcR, ENNReal.ofReal_natCast]]
      rw [← ENNReal.ofReal_mul (inv_nonneg.2 hcR.le)]
      congr 1
      rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
      field_simp
    · have hC0 : C = ∅ := Finset.card_eq_zero.mp (by omega)
      subst hC0
      rw [attemptM, dif_neg hC]
      simp [attemptProbNodes]

theorem attemptM_some_good (gs : List (Fin S.graph.size))
    (hgs : ∀ v ∈ gs, (S.graph.kind v).IsHash) (C : Finset S.graph.Rec) (ξ' : S.graph.Rec)
    (h : Pr[= some ξ' | simulateQ (tableImpl P (decode S) g) (attemptM S C gs)] ≠ 0) :
    ξ' ∈ C ∧ ∀ v ∈ gs,
      graphTab S g v ((S.graph.kind v).input (S.graph.evalRec ξ')) = ξ'.2 v := by
  induction gs generalizing C with
  | nil =>
    unfold attemptM at h
    simp only [simulateQ_pure, probOutput_pure] at h
    by_cases h1 : C.Nonempty
    · rw [dif_pos h1] at h
      by_cases h2 : ξ' = Classical.choose h1
      · subst h2
        exact ⟨Classical.choose_spec h1, by simp⟩
      · simp [h2] at h
    · rw [dif_neg h1] at h
      simp at h
  | cons v gs ih =>
    by_cases hC : 0 < C.card
    · rw [← probEvent_eq_eq_probOutput, probEvent_attemptM_cons S g v (hgs v (by simp)) gs C hC]
        at h
      obtain ⟨ξ, -, hξ⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
      have h2 := right_ne_zero_of_mul hξ
      rw [probEvent_eq_eq_probOutput] at h2
      obtain ⟨hm, hg⟩ := ih (fun w hw => hgs w (by simp [hw])) _ h2
      simp only [Finset.mem_filter] at hm
      refine ⟨hm.1, ?_⟩
      intro w hw
      simp only [List.mem_cons] at hw
      rcases hw with rfl | hw
      · rw [hm.2.1, hm.2.2]
      · exact hg w hw
    · rw [attemptM, dif_neg hC] at h
      simp at h

/-- The success event of the construction attempts. -/
def AttGood (C : Finset S.graph.Rec) (gs : List (Fin S.graph.size)) (r : Option S.graph.Rec) :
    Prop :=
  ∃ ξ', r = some ξ' ∧ ξ' ∈ C ∧ ∀ v ∈ gs,
    graphTab S g v ((S.graph.kind v).input (S.graph.evalRec ξ')) = ξ'.2 v

theorem probEvent_attempts (C : Finset S.graph.Rec) (gs : List (Fin S.graph.size))
    (hgs : ∀ v ∈ gs, (S.graph.kind v).IsHash) (n : ℕ) :
    ENNReal.ofReal (1 - (1 - attemptProbNodes S (graphTab S g) gs C) ^ n) ≤
      Pr[AttGood S g C gs | simulateQ (tableImpl P (decode S) g) (attempts S C gs n)] := by
  set p := attemptProbNodes S (graphTab S g) gs C with hp
  have hp01 : 0 ≤ p ∧ p ≤ 1 := attemptProbNodes_mem S (graphTab S g) gs C
  induction n with
  | zero => simp
  | succ n ih =>
    rw [attempts, simulateQ_bind, probEvent_bind_eq_tsum, ENNReal.tsum_eq_add_tsum_ite none]
    set M := simulateQ (tableImpl P (decode S) g) (attemptM S C gs) with hM
    have hnone : Pr[= none | M] = ENNReal.ofReal (1 - p) := probOutput_attemptM_none S g gs hgs C
    have htot : Pr[= none | M] + ∑' r, (if r = none then 0 else Pr[= r | M]) = 1 := by
      have h := ENNReal.tsum_eq_add_tsum_ite (f := fun r => Pr[= r | M]) none
      have h1 : ∑' r, Pr[= r | M] = 1 := by simp
      rw [h1] at h
      convert h.symm
    have hrest : ∑' r, (if r = none then 0 else Pr[= r | M]) = ENNReal.ofReal p := by
      rw [hnone] at htot
      have h1 : ENNReal.ofReal (1 - p) + ENNReal.ofReal p = 1 := by
        rw [← ENNReal.ofReal_add (by linarith) hp01.1]
        simp
      exact (ENNReal.add_right_inj ENNReal.ofReal_ne_top).1 (htot.trans h1.symm)
    calc ENNReal.ofReal (1 - (1 - p) ^ (n + 1))
        = ENNReal.ofReal (1 - p) * ENNReal.ofReal (1 - (1 - p) ^ n) + ENNReal.ofReal p := by
          have hq : (1 - p) ^ n ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
          rw [← ENNReal.ofReal_mul (by linarith),
            ← ENNReal.ofReal_add (mul_nonneg (by linarith) (by linarith)) hp01.1]
          congr 1
          ring
      _ ≤ _ := by
          rw [← hnone]
          gcongr
          refine le_trans (le_of_eq hrest.symm) (ENNReal.tsum_le_tsum fun r => ?_)
          rcases r with _ | ξ'
          · simp
          · simp only [reduceCtorEq, if_false, simulateQ_pure]
            rcases eq_or_ne (Pr[= some ξ' | M]) 0 with h0 | h0
            · rw [h0, zero_mul]
            · obtain ⟨hm, hg⟩ := attemptM_some_good S g gs hgs C ξ' h0
              rw [probEvent_pure, if_pos ⟨ξ', rfl, hm, hg⟩, mul_one]

/-! ## Bit strings and the revealed values -/

theorem testBit_foldr (l : List Bool) (i : ℕ) :
    (l.foldr (fun (b : Bool) (acc : ℕ) => b.toNat + 2 * acc) 0).testBit i = l.getD i false := by
  induction l generalizing i with
  | nil => simp
  | cons b l ih =>
    rw [List.foldr_cons]
    rcases i with _ | i
    · rw [Nat.testBit_zero]
      cases b <;> simp [Nat.add_mul_mod_self_left]
    · rw [Nat.testBit_succ, List.getD_cons_succ, ← ih i]
      congr 1
      cases b <;> simp <;> omega

theorem ofBits_toBits {n : ℕ} (x : BitVec n) : ofBits n (toBits x) = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [ofBits, BitVec.getLsbD_ofNat, toBits]
  rw [testBit_foldr]
  simp [hi, List.getD_eq_getElem?_getD]

theorem length_toBits {n : ℕ} (x : BitVec n) : (toBits x).length = n := List.length_ofFn

theorem flatMap_split {n : ℕ} {β : Type} (f : Fin n → List β) (L : List (Fin n))
    (hL : L.Pairwise (· < ·)) (v : Fin n) (hv : v ∈ L) :
    L.flatMap f = (L.filter fun w => decide (w < v)).flatMap f ++ f v ++
      (L.filter fun w => decide (v < w)).flatMap f := by
  induction L with
  | nil => simp at hv
  | cons a L ih =>
    rw [List.pairwise_cons] at hL
    rcases List.mem_cons.1 hv with rfl | hv'
    · have h1 : (L.filter fun w => decide (w < v)) = [] := by
        rw [List.filter_eq_nil_iff]
        intro w hw
        simpa using le_of_lt (hL.1 w hw)
      have h2 : (L.filter fun w => decide (v < w)) = L := by
        rw [List.filter_eq_self]
        intro w hw
        simpa using hL.1 w hw
      simp [List.filter_cons, h1, h2]
    · have hav : a < v := hL.1 v hv'
      rw [List.flatMap_cons, ih hL.2 hv']
      simp [List.filter_cons, hav, not_lt.2 hav.le]

section Generic

variable {G : Graph P}

theorem length_encode (A : Finset (Fin G.size)) (x : G.Assignment) :
    (G.encode A x).length = G.revealBits A := by
  unfold Graph.encode Graph.revealBits
  rw [List.length_flatMap]
  simp only [length_toBits]
  rw [← List.sum_toFinset _ ((List.nodup_finRange _).filter _)]
  congr 1
  ext v
  simp

theorem decode_encode (A : Finset (Fin G.size)) (x : G.Assignment) (v : Fin G.size)
    (hv : v ∈ A) : G.decode A (G.encode A x) v = x v := by
  unfold Graph.decode Graph.encode
  have hL : ((List.finRange G.size).filter fun w => decide (w ∈ A)).Pairwise (· < ·) :=
    (List.pairwise_lt_finRange _).filter _
  rw [flatMap_split _ _ hL v (by simp [hv])]
  have hoff : G.offset A v = ((((List.finRange G.size).filter fun w => decide (w ∈ A)).filter
      fun w => decide (w < v)).flatMap (fun w => toBits (x w))).length := by
    rw [List.length_flatMap]
    simp only [length_toBits]
    unfold Graph.offset
    rw [← List.sum_toFinset _ (((List.nodup_finRange _).filter _).filter _)]
    congr 1
    ext w
    simp [and_comm]
  rw [hoff, List.append_assoc, List.drop_left, List.take_left' (length_toBits _), ofBits_toBits]

end Generic

/-! ## Node kinds -/

theorem value_ne_source {v : Fin S.graph.size} (x : S.graph.Assignment)
    (s s' : BitVec (S.graph.len v)) (a : BitVec P.hashBits) (h : ¬ (S.graph.kind v).IsSource) :
    (S.graph.kind v).value x s a = (S.graph.kind v).value x s' a := by
  revert h
  generalize S.graph.kind v = k
  cases k <;> intro h
  · exact absurd trivial h
  · rfl
  · rfl

theorem value_nonHash {v : Fin S.graph.size} (x : S.graph.Assignment)
    (s : BitVec (S.graph.len v)) (a a' : BitVec P.hashBits) (h : ¬ (S.graph.kind v).IsHash) :
    (S.graph.kind v).value x s a = (S.graph.kind v).value x s a' := by
  revert h
  generalize S.graph.kind v = k
  cases k <;> intro h
  · rfl
  · rfl
  · exact absurd trivial h

theorem output_value_hash {v : Fin S.graph.size} (x : S.graph.Assignment)
    (s : BitVec (S.graph.len v)) (a : BitVec P.hashBits) (h : (S.graph.kind v).IsHash) :
    (S.graph.kind v).output ((S.graph.kind v).value x s a) = a := by
  revert h
  generalize S.graph.kind v = k
  cases k <;> intro h
  · exact absurd h id
  · exact absurd h id
  · simp [NodeKind.output, NodeKind.value]

theorem input_congr {v : Fin S.graph.size} (x y : S.graph.Assignment)
    (h : ∀ w ∈ (S.graph.kind v).parents, x w = y w) :
    (S.graph.kind v).input x = (S.graph.kind v).input y := by
  revert h
  generalize S.graph.kind v = k
  cases k <;> intro h
  · rfl
  · rfl
  · exact h _ (by simp [NodeKind.parents])

theorem evalTab_apply (z : S.graph.Assignment) (t : S.graph.Tab) (v : Fin S.graph.size) :
    S.graph.evalTab z t v = (S.graph.kind v).value (S.graph.evalTab z t) (z v)
      (t v ((S.graph.kind v).input (S.graph.evalTab z t))) :=
  S.graph.evalWith_apply (S.graph.parentLocal_tabVal z t) v

theorem mem_evalHashAt (i : Fin P.numSets) (v : Fin S.graph.size) :
    v ∈ evalHashAt S i ↔
      S.graph.Visited (S.sets i) v ∧ v ∉ S.sets i ∧ (S.graph.kind v).IsHash := by
  simp [evalHashAt, Graph.evalHash, Graph.evaluated, and_assoc]

theorem mem_newNodes (i j : Fin P.numSets) (v : Fin S.graph.size) :
    v ∈ newNodes S i j ↔ v ∈ evalHashAt S j ∧ v ∉ evalHashAt S i := by
  simp [newNodes]

theorem reconTab_congr (tg : S.graph.Tab) (A : Finset (Fin S.graph.size))
    (given given' : S.graph.Assignment) (h : ∀ v ∈ A, given v = given' v) :
    S.graph.reconTab tg A given = S.graph.reconTab tg A given' := by
  unfold Graph.reconTab
  congr 1
  funext v x
  simp only [Graph.reconVal]
  split_ifs with hv
  · exact h v hv
  · rfl
  · rfl

theorem reconTab_decode_encode_eq (tg : S.graph.Tab) (i : Fin P.numSets) (a : S.graph.Assignment)
    (ha : ∀ v, S.graph.Visited (S.sets i) v → v ∉ S.sets i →
      a v = (S.graph.kind v).value a 0 (tg v ((S.graph.kind v).input a)))
    (v : Fin S.graph.size) (hv : S.graph.Visited (S.sets i) v) :
    S.graph.reconTab tg (S.sets i) (S.graph.decode (S.sets i) (S.graph.encode (S.sets i) a)) v =
      a v := by
  rw [reconTab_congr S tg _ _ a (fun w hw => decode_encode _ a w hw)]
  exact S.graph.reconTab_eq_of_visited tg _ a (S.no_hidden_source i) ha v hv

theorem evalTab_nodeEqs (z : S.graph.Assignment) (tg : S.graph.Tab) (i : Fin P.numSets) :
    ∀ v, S.graph.Visited (S.sets i) v → v ∉ S.sets i →
      S.graph.evalTab z tg v = (S.graph.kind v).value (S.graph.evalTab z tg) 0
        (tg v ((S.graph.kind v).input (S.graph.evalTab z tg))) := by
  intro v hv hA
  conv_lhs => rw [evalTab_apply]
  exact value_ne_source S _ _ _ _ (S.no_hidden_source i v hv hA)

/-! ## Candidates -/

theorem mem_obsCands (i : Fin P.numSets) (ξ ξ' : S.graph.Rec) :
    ξ' ∈ obsCands S i ξ ↔
      reveal S i ξ' = reveal S i ξ ∧ ∀ k ∈ evalHashAt S i, ξ'.2 k = ξ.2 k := by
  unfold obsCands candidates
  convert Finset.mem_filter (s := (Finset.univ : Finset S.graph.Rec)) (a := ξ') using 1
  simp

theorem mem_cands (i : Fin P.numSets) (xa xr : S.graph.Assignment) (ξ' : S.graph.Rec) :
    ξ' ∈ cands S i xa xr ↔
      (∀ v ∈ S.sets i, S.graph.evalRec ξ' v = xa v) ∧
        ∀ g ∈ evalHashAt S i, ξ'.2 g = (S.graph.kind g).output (xr g) :=
  ⟨fun h => (Finset.mem_filter.1 h).2, fun h => Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩⟩

theorem cand_agree (i : Fin P.numSets) (ξ ξ' : S.graph.Rec) (h : ξ' ∈ obsCands S i ξ) :
    ∀ v, S.graph.Visited (S.sets i) v → S.graph.evalRec ξ' v = S.graph.evalRec ξ v := by
  obtain ⟨hrev, hout⟩ := (mem_obsCands S i ξ ξ').1 h
  intro v
  induction v using WellFoundedLT.induction with
  | _ v ih =>
    intro hv
    by_cases hA : v ∈ S.sets i
    · exact congrFun hrev ⟨v, hA⟩
    · have hns := S.no_hidden_source i v hv hA
      rw [S.graph.evalRec_apply ξ', S.graph.evalRec_apply ξ,
        value_ne_source S _ (ξ'.1 v) (ξ.1 v) _ hns]
      have h2 : (S.graph.kind v).value (S.graph.evalRec ξ') (ξ.1 v) (ξ'.2 v) =
          (S.graph.kind v).value (S.graph.evalRec ξ') (ξ.1 v) (ξ.2 v) := by
        by_cases hh : (S.graph.kind v).IsHash
        · rw [hout v ((mem_evalHashAt S i v).2 ⟨hv, hA, hh⟩)]
        · exact value_nonHash S _ _ _ _ hh
      rw [h2]
      exact NodeKind.value_congr _ _ _ _ _ fun w hw =>
        ih w ((S.graph.kind v).lt_of_mem_parents hw) (Graph.Visited.parent hv hA hw)

theorem cands_eq (i : Fin P.numSets) (z : S.graph.Assignment) (tg : S.graph.Tab) :
    cands S i (S.graph.decode (S.sets i) (S.graph.encode (S.sets i) (S.graph.evalTab z tg)))
      (S.graph.reconTab tg (S.sets i)
        (S.graph.decode (S.sets i) (S.graph.encode (S.sets i) (S.graph.evalTab z tg)))) =
    obsCands S i (S.graph.recOf z tg) := by
  have hxr := reconTab_decode_encode_eq S tg i _ (evalTab_nodeEqs S z tg i)
  ext ξ'
  rw [mem_cands, mem_obsCands]
  apply and_congr
  · rw [funext_iff]
    constructor
    · rintro h ⟨v, hv⟩
      change S.graph.evalRec ξ' v = S.graph.evalRec (S.graph.recOf z tg) v
      rw [Graph.evalRec_recOf, h v hv, decode_encode _ _ v hv]
    · intro h v hv
      have h' : S.graph.evalRec ξ' v = S.graph.evalRec (S.graph.recOf z tg) v := h ⟨v, hv⟩
      rw [h', Graph.evalRec_recOf, decode_encode _ _ v hv]
  · apply forall₂_congr
    intro v hv
    have hv' := (mem_evalHashAt S i v).1 hv
    rw [hxr v hv'.1]
    conv_lhs => rw [evalTab_apply]
    rw [output_value_hash S _ _ _ hv'.2.2]
    rfl

theorem forged_nodeEqs (i j : Fin P.numSets) (z : S.graph.Assignment) (tg : S.graph.Tab)
    (ξ' : S.graph.Rec) (hc : ξ' ∈ obsCands S i (S.graph.recOf z tg))
    (hg : ∀ v ∈ newNodes S i j,
      tg v ((S.graph.kind v).input (S.graph.evalRec ξ')) = ξ'.2 v) :
    ∀ v, S.graph.Visited (S.sets j) v → v ∉ S.sets j →
      S.graph.evalRec ξ' v = (S.graph.kind v).value (S.graph.evalRec ξ') 0
        (tg v ((S.graph.kind v).input (S.graph.evalRec ξ'))) := by
  intro v hv hA
  have hns := S.no_hidden_source j v hv hA
  conv_lhs => rw [S.graph.evalRec_apply ξ']
  rw [value_ne_source S _ (ξ'.1 v) 0 _ hns]
  by_cases hh : (S.graph.kind v).IsHash
  · congr 1
    by_cases hi : v ∈ evalHashAt S i
    · have hout := ((mem_obsCands S i _ ξ').1 hc).2 v hi
      rw [hout]
      have hi' := (mem_evalHashAt S i v).1 hi
      change tg v ((S.graph.kind v).input (S.graph.evalTab z tg)) = _
      rw [← Graph.evalRec_recOf]
      exact congrArg (tg v) (input_congr S _ _ fun w hw =>
        (cand_agree S i _ ξ' hc w (Graph.Visited.parent hi'.1 hi'.2.1 hw)).symm)
    · exact (hg v ((mem_newNodes S i j v).2 ⟨(mem_evalHashAt S j v).2 ⟨hv, hA, hh⟩, hi⟩)).symm
  · exact value_nonHash S _ _ _ _ hh

theorem forged_root (i : Fin P.numSets) (z : S.graph.Assignment) (tg : S.graph.Tab)
    (ξ' : S.graph.Rec) (hc : ξ' ∈ obsCands S i (S.graph.recOf z tg)) :
    S.graph.evalRec ξ' S.graph.root = S.graph.evalTab z tg S.graph.root := by
  rw [cand_agree S i _ ξ' hc _ Graph.Visited.root, Graph.evalRec_recOf]

theorem sim_verify_true (j : Fin P.numSets) (η₂ : Nonce P) (a x : S.graph.Assignment)
    (hidx : idxOfOut P (nonceTab S g (msg₂ P) η₂) = j.val)
    (ha : ∀ v, S.graph.Visited (S.sets j) v → v ∉ S.sets j →
      a v = (S.graph.kind v).value a 0 (graphTab S g v ((S.graph.kind v).input a)))
    (hroot : a S.graph.root = x S.graph.root) :
    simulateQ (tableImpl P (decode S) g)
      (S.verify (S.publicKey x) (msg₂ P) (η₂, S.graph.encode (S.sets j) a)) = pure true := by
  unfold Scheme.verify
  simp only [simulateQ_bind, sim_index, pure_bind]
  generalize idxOfOut P (nonceTab S g (msg₂ P) η₂) = n at hidx ⊢
  subst hidx
  rw [dif_pos j.isLt]
  simp only [Fin.eta, length_encode, if_true, simulateQ_bind, sim_reconstruct, pure_bind,
    simulateQ_pure]
  simp [Scheme.publicKey, reconTab_decode_encode_eq S _ j a ha _ Graph.Visited.root, hroot]

/-! ## Assembly -/

theorem succ_le_one (q : ℕ) (i : Fin P.numSets) (ℓ : ℕ) (z : S.graph.Assignment)
    (t : S.graph.Tab) : succ S q i ℓ z t ≤ 1 := by
  unfold succ
  dsimp only
  split_ifs
  · exact le_rfl
  · exact sub_le_self _ (pow_nonneg (sub_nonneg.2 (attemptProbNodes_mem S _ _ _).2) _)

theorem sum_pairs_le_tsum (x : S.graph.Assignment) (u : Nonce P → BitVec P.hashBits)
    (F : Option (Signature P) → ℝ≥0∞) :
    ∑ i : Fin P.numSets, ∑ η : Nonce P,
      (if idxOfOut P (u η) = i.val then F (some (η, S.graph.encode (S.sets i) x)) else 0) ≤
      ∑' σ, F σ := by
  have h1 : ∑ i : Fin P.numSets, ∑ η : Nonce P,
      (if idxOfOut P (u η) = i.val then F (some (η, S.graph.encode (S.sets i) x)) else 0) =
      ∑ p ∈ (Finset.univ : Finset (Fin P.numSets × Nonce P)).filter
        (fun p => idxOfOut P (u p.2) = p.1.val),
        F (some (p.2, S.graph.encode (S.sets p.1) x)) := by
    rw [Finset.sum_filter, ← Finset.univ_product_univ, Finset.sum_product]
  rw [h1, ← Finset.sum_image (f := F)
    (g := fun p : Fin P.numSets × Nonce P => (some (p.2, S.graph.encode (S.sets p.1) x) :
      Option (Signature P)))]
  · exact ENNReal.sum_le_tsum _
  · rintro ⟨i, η⟩ hp ⟨i', η'⟩ hp' h
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hp hp'
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Prod.ext (Fin.ext (hp.symm.trans hp')) rfl

theorem probOutput_bind_ge_of_event {α : Type} (mx : ProbComp α) (k : α → ProbComp Bool)
    (E : α → Prop) (hk : ∀ a, E a → Pr[= true | k a] = 1) :
    Pr[E | mx] ≤ Pr[= true | mx >>= k] := by
  rw [probEvent_eq_tsum_ite, probOutput_bind_eq_tsum]
  refine ENNReal.tsum_le_tsum fun a => ?_
  split_ifs with h
  · rw [hk a h, mul_one]
  · exact zero_le

theorem forge_stage (q T : ℕ) (h12 : msg₁ P ≠ msg₂ P) (z : S.graph.Assignment)
    (i : Fin P.numSets) (η₁ : Nonce P) (hη : idxOfOut P (nonceTab S g (msg₁ P) η₁) = i.val) :
    (∑ ℓ ∈ Finset.range 100,
        (if bestPure P T (rkOf S i (obsCands S i (S.graph.recOf z (graphTab S g))))
            (nonceTab S g (msg₂ P)) = some ℓ then 1 else 0) *
          ENNReal.ofReal (succ S q i ℓ z (graphTab S g))) ≤
      Pr[= true | simulateQ (tableImpl P (decode S) g)
          (forge S q T (some (η₁, S.graph.encode (S.sets i) (S.graph.evalTab z (graphTab S g))))) >>=
        fun x_2 => simulateQ (tableImpl P (decode S) g)
          (S.verify (S.publicKey (S.graph.evalTab z (graphTab S g))) x_2.1 x_2.2) >>= fun b =>
            pure (b && ((some (η₁, S.graph.encode (S.sets i)
              (S.graph.evalTab z (graphTab S g)))).isNone || decide (x_2.1 ≠ msg₁ P)))] := by
  set C := obsCands S i (S.graph.recOf z (graphTab S g)) with hC
  rcases hb : bestPure P T (rkOf S i C) (nonceTab S g (msg₂ P)) with _ | ℓ
  · simp
  have hsum : ∀ ℓ' ∈ Finset.range 100, (if some ℓ = some ℓ' then (1 : ℝ≥0∞) else 0) *
      ENNReal.ofReal (succ S q i ℓ' z (graphTab S g)) =
      if ℓ' = ℓ then ENNReal.ofReal (succ S q i ℓ z (graphTab S g)) else 0 := by
    intro ℓ' _
    by_cases h : ℓ' = ℓ
    · subst h; simp
    · simp [Ne.symm h, h]
  rw [Finset.sum_congr rfl hsum, Finset.sum_ite_eq']
  refine le_trans (by split_ifs <;> simp) (?_ : ENNReal.ofReal (succ S q i ℓ z (graphTab S g)) ≤ _)
  obtain ⟨j, η₂, hs, hrank, hidx⟩ := search_spec S T i C _ hb
  have hℓ : ℓ < P.numSets := hrank ▸ rank_lt S i C j
  have hj : rankElem S i C ℓ = j :=
    rank_injective S i C ((rank_rankElem S i C hℓ).trans hrank.symm)
  simp only [forge, simulateQ_bind, sim_index, pure_bind]
  generalize idxOfOut P (nonceTab S g (msg₁ P) η₁) = n at hη ⊢
  subst hη
  rw [dif_pos i.isLt]
  simp only [Fin.eta, simulateQ_bind, sim_reconstruct, pure_bind, cands_eq, sim_search, ← hC, hs]
  by_cases hji : j = i
  · subst hji
    simp only [if_true, simulateQ_pure, pure_bind]
    rw [sim_verify_true S g j η₂ _ _ hidx (evalTab_nodeEqs S z _ j) rfl]
    simp [h12.symm, succ_le_one]
  · simp only [if_neg hji, simulateQ_bind, bind_assoc]
    have hsucc : succ S q i ℓ z (graphTab S g) =
        1 - (1 - attemptProbNodes S (graphTab S g) (newNodes S i j) C) ^ q := by
      simp only [succ, ← hC, hj, if_neg hji]
    rw [hsucc]
    have hgs : ∀ v ∈ newNodes S i j, (S.graph.kind v).IsHash := fun v hv =>
      ((mem_evalHashAt S j v).1 ((mem_newNodes S i j v).1 hv).1).2.2
    refine le_trans (probEvent_attempts S g C (newNodes S i j) hgs q)
      (probOutput_bind_ge_of_event _ _ _ ?_)
    rintro r ⟨ξ', rfl, hm, hg⟩
    simp only [simulateQ_pure, pure_bind]
    rw [sim_verify_true S g j η₂ _ _ hidx (forged_nodeEqs S i j z _ ξ' hm hg)
      (forged_root S i z _ ξ' hm)]
    simp [h12.symm]

theorem probOutput_sampleAssignment (z : S.graph.Assignment) :
    Pr[= z | simulateQ (tableImpl P (decode S) g) S.graph.sampleAssignment] =
      (Fintype.card S.graph.Assignment : ℝ≥0∞)⁻¹ := by
  unfold Graph.sampleAssignment
  rw [probOutput_foldl_sample S g _ (List.nodup_finRange _),
    if_pos (fun v hv => absurd (List.mem_finRange v) hv), ← Fin.prod_univ_def,
    Fintype.card_pi, Nat.cast_prod,
    ENNReal.prod_inv_distrib (fun _ _ _ _ _ => Or.inr (ENNReal.natCast_ne_top _))]

end Decomp

open Decomp in
theorem sum_le_probOutput_table (q T : ℕ) (h12 : Attack.msg₁ P ≠ Attack.msg₂ P)
    (g : Cell S → BitVec P.hashBits) :
    (∑ z : S.graph.Assignment, ∑ i : Fin P.numSets,
        signProb S (nonceTab S g (Attack.msg₁ P)) (S.graph.evalTab z (graphTab S g)) i *
          ∑ ℓ ∈ Finset.range 100,
            (if bestPure P T (rkOf S i (obsCands S i (S.graph.recOf z (graphTab S g))))
                (nonceTab S g (Attack.msg₂ P)) = some ℓ then 1 else 0) *
              ENNReal.ofReal (succ S q i ℓ z (graphTab S g))) /
        (Fintype.card S.graph.Assignment : ℝ≥0∞) ≤
      Pr[= true | simulateQ (tableImpl P (decode S) g)
        (weakExperiment S (Attack.adversary S q T))] := by
  simp only [weakExperiment, Scheme.keygen, Graph.keygen, simulateQ_bind, simulateQ_pure, bind_assoc,
    pure_bind, Attack.adversary]
  rw [probOutput_bind_eq_tsum, tsum_fintype, ENNReal.div_eq_inv_mul, Finset.mul_sum]
  refine Finset.sum_le_sum fun z _ => ?_
  rw [probOutput_sampleAssignment S g z, sim_evaluate, pure_bind]
  refine mul_le_mul_of_nonneg_left ?_ zero_le
  rw [probOutput_bind_eq_tsum, show simulateQ (tableImpl P (decode S) g)
      (S.sign (S.graph.evalTab z (graphTab S g)) (msg₁ P)) =
    simulateQ (signImpl P (nonceTab S g (msg₁ P)))
      (S.sign (S.graph.evalTab z (graphTab S g)) (msg₁ P)) from sim_signLoop S g _ _ _]
  refine le_trans ?_ (sum_pairs_le_tsum S (S.graph.evalTab z (graphTab S g))
    (nonceTab S g (msg₁ P)) _)
  unfold signProb
  simp only [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun η _ => ?_
  split_ifs with h
  · exact mul_le_mul_of_nonneg_left (forge_stage S g q T h12 z i η h) zero_le
  · simp

end Analysis
end OptimalOTS
