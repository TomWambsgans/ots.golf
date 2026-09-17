import Submissions.Lower.AnalysisDefs
import OptimalOTS.Statement
import Submissions.Lower.NumericsDefs
import Submissions.Lower.Construction
import Submissions.Lower.Repetition
import Submissions.Lower.Numerics
import Submissions.Lower.EntropyLemmas

/-!
# Construction success averaged over key generation

For a fixed index `i` and rank `ℓ`, the success probability of the forging step, averaged over
the sources and the graph tables, is at least the average of `max 0 (1 - D/113)` over records.
-/

open OracleSpec OracleComp ENNReal

noncomputable section

open scoped Classical

namespace OptimalOTS

namespace Analysis

namespace AvgSuccAux

/-- Averaging over classes of an equivalence relation. -/
theorem sum_eq_sum_class_avg {α : Type*} [Fintype α] (cl : α → Finset α) (hmem : ∀ a, a ∈ cl a)
    (hcl : ∀ a b, b ∈ cl a → cl b = cl a) (H : α → ℝ) :
    ∑ a, H a = ∑ a, (∑ b ∈ cl a, H b) / ((cl a).card : ℝ) := by
  have hsymm : ∀ a b, b ∈ cl a ↔ a ∈ cl b := fun a b =>
    ⟨fun h => hcl a b h ▸ hmem a, fun h => hcl b a h ▸ hmem b⟩
  have h1 : ∀ a, (∑ b ∈ cl a, H b) / ((cl a).card : ℝ) =
      ∑ b, if a ∈ cl b then H b / ((cl b).card : ℝ) else 0 := by
    intro a
    rw [Finset.sum_div, ← Finset.sum_filter]
    have e : (Finset.univ.filter fun b => a ∈ cl b) = cl a := by
      ext b; simp [← hsymm]
    rw [e]
    refine Finset.sum_congr rfl fun b hb => ?_
    rw [hcl a b hb]
  simp_rw [h1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  have hpos : (0 : ℝ) < ((cl b).card : ℝ) := by exact_mod_cast Finset.card_pos.2 ⟨b, hmem b⟩
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have : (Finset.univ.filter fun a => a ∈ cl b) = cl b := by ext; simp
  rw [this]
  field_simp

/-- Restricting tables to a subset of the coordinates: the average over consistent tables of a
function of the restriction equals the average over consistent restrictions. -/
theorem avg_restrict_filter {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] {β : ι → Type*}
    [∀ i, Fintype (β i)] (p : ι → Prop) [DecidablePred p] (σ : κ ≃ {i // p i})
    (Q : ∀ i, β i → Prop) (hQ : ∀ i, ∃ x, Q i x) (f : ((k : κ) → β (σ k).1) → ℝ) :
    (∑ t ∈ Finset.univ.filter (fun t : (∀ i, β i) => ∀ i, Q i (t i)),
        f (fun k => t (σ k).1)) /
      ((Finset.univ.filter (fun t : (∀ i, β i) => ∀ i, Q i (t i))).card : ℝ) =
    (∑ a ∈ Finset.univ.filter (fun a : ((k : κ) → β (σ k).1) => ∀ k, Q _ (a k)), f a) /
      ((Finset.univ.filter (fun a : ((k : κ) → β (σ k).1) => ∀ k, Q _ (a k))).card : ℝ) := by
  let e : (∀ i, β i) ≃ ((k : κ) → β (σ k).1) × ((i : {i // ¬ p i}) → β i.1) :=
    (Equiv.piEquivPiSubtypeProd p β).trans
      (Equiv.prodCongr (Equiv.piCongrLeft (fun i : {i // p i} => β i.1) σ).symm (Equiv.refl _))
  have he1 : ∀ t k, (e t).1 k = t (σ k).1 := fun t k => rfl
  have he2 : ∀ t i, (e t).2 i = t i.1 := fun t i => rfl
  have hiff : ∀ t, (∀ i, Q i (t i)) ↔ (∀ k, Q _ ((e t).1 k)) ∧ ∀ i, Q _ ((e t).2 i) := by
    intro t
    simp only [he1, he2]
    refine ⟨fun h => ⟨fun k => h _, fun i => h _⟩, fun h i => ?_⟩
    by_cases hi : p i
    · have := h.1 (σ.symm ⟨i, hi⟩)
      rw [Equiv.apply_symm_apply] at this
      exact this
    · exact h.2 ⟨i, hi⟩
  have key : ∀ g : ((k : κ) → β (σ k).1) → ℝ,
      ∑ t ∈ Finset.univ.filter (fun t : (∀ i, β i) => ∀ i, Q i (t i)), g (fun k => t (σ k).1) =
      (∑ a ∈ Finset.univ.filter (fun a : ((k : κ) → β (σ k).1) => ∀ k, Q _ (a k)), g a) *
        ((Finset.univ.filter (fun r : ((i : {i // ¬ p i}) → β i.1) => ∀ i, Q _ (r i))).card : ℝ) := by
    intro g
    rw [Finset.sum_filter, Finset.sum_filter, Finset.card_filter, Nat.cast_sum, Finset.sum_mul_sum,
      ← Finset.sum_product']
    rw [← e.symm.sum_comp]
    refine Finset.sum_congr (by simp) fun x _ => ?_
    have h1 : (fun k => (e.symm x) (σ k).1) = x.1 := by
      change (fun k => (e (e.symm x)).1 k) = x.1
      rw [Equiv.apply_symm_apply]
    have h2 := hiff (e.symm x)
    rw [Equiv.apply_symm_apply] at h2
    simp only [h1]
    by_cases hA : ∀ k, Q _ (x.1 k) <;> by_cases hB : ∀ i, Q _ (x.2 i) <;> simp [hA, hB, h2]
  have hR : 0 < (Finset.univ.filter (fun r : ((i : {i // ¬ p i}) → β i.1) => ∀ i, Q _ (r i))).card := by
    refine Finset.card_pos.2 ⟨fun i => (hQ i.1).choose, ?_⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact fun i => (hQ i.1).choose_spec
  have hR' : (0 : ℝ) < ((Finset.univ.filter (fun r : ((i : {i // ¬ p i}) → β i.1) => ∀ i, Q _ (r i))).card : ℝ) := by
    exact_mod_cast hR
  have hc := key (fun _ => 1)
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at hc
  rw [key f, hc, mul_div_mul_right _ _ hR'.ne']


theorem avg_restrict {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] {β : ι → Type*}
    [∀ i, Fintype (β i)] (p : ι → Prop) [DecidablePred p] (σ : κ ≃ {i // p i})
    (Q : ∀ i, β i → Prop) (hQ : ∀ i, ∃ x, Q i x) (f : ((k : κ) → β (σ k).1) → ℝ)
    (A : Finset (∀ i, β i)) (hA : ∀ t, t ∈ A ↔ ∀ i, Q i (t i))
    (B : Finset ((k : κ) → β (σ k).1)) (hB : ∀ a, a ∈ B ↔ ∀ k, Q _ (a k)) :
    (∑ t ∈ A, f (fun k => t (σ k).1)) / (A.card : ℝ) = (∑ a ∈ B, f a) / (B.card : ℝ) := by
  have eA : A = Finset.univ.filter (fun t : (∀ i, β i) => ∀ i, Q i (t i)) := by
    ext t; simp [hA]
  have eB : B = Finset.univ.filter (fun a : ((k : κ) → β (σ k).1) => ∀ k, Q _ (a k)) := by
    ext a; simp [hB]
  subst eA eB
  exact avg_restrict_filter p σ Q hQ f

section Scheme

open Attack

variable {P : Params} (S : Scheme P)

theorem weight_nonneg' (i : Fin P.numSets) (C : Finset S.graph.Rec) (g : Fin S.graph.size) :
    0 ≤ weight S i C g := by
  unfold weight
  split_ifs
  · exact le_rfl
  · exact sub_nonneg.mpr (condEntropy_le_logb_card _ _ _)

theorem targetWeight_nonneg' (i : Fin P.numSets) (C : Finset S.graph.Rec) (j : Fin P.numSets) :
    0 ≤ targetWeight S i C j :=
  Finset.sum_nonneg fun g _ => weight_nonneg' S i C g

/-- The tables consistent with a record. -/
def consTabs (ξ : S.graph.Rec) : Finset S.graph.Tab :=
  Finset.univ.filter fun t => S.graph.Consistent ξ t

theorem sum_recOf (F : S.graph.Rec → S.graph.Tab → ℝ) :
    ∑ z : S.graph.Assignment, ∑ t : S.graph.Tab, F (S.graph.recOf z t) t =
      ∑ ξ : S.graph.Rec, ∑ t ∈ consTabs S ξ, F ξ t := by
  simp_rw [consTabs, Finset.sum_filter]
  rw [Finset.sum_comm, Finset.sum_comm (s := (Finset.univ : Finset S.graph.Rec))]
  refine Finset.sum_congr rfl fun t _ => ?_
  calc ∑ z : S.graph.Assignment, F (S.graph.recOf z t) t
      = ∑ z : S.graph.Assignment, ∑ ξ : S.graph.Rec,
          if S.graph.recOf z t = ξ then F ξ t else 0 := by
        refine Finset.sum_congr rfl fun z _ => ?_
        rw [Finset.sum_ite_eq]; simp
    _ = ∑ ξ : S.graph.Rec, ∑ z : S.graph.Assignment,
          if S.graph.recOf z t = ξ then F ξ t else 0 := Finset.sum_comm
    _ = _ := by
        refine Finset.sum_congr rfl fun ξ _ => ?_
        simp_rw [Graph.recOf_eq_iff, ite_and]
        rw [Finset.sum_ite_eq']
        simp

theorem card_consTabs (ξ : S.graph.Rec) :
    ((consTabs S ξ).card : ℝ) =
      (Fintype.card S.graph.Tab : ℝ) / (Fintype.card (BitVec P.hashBits) : ℝ) ^ S.graph.size := by
  have h := card_tables_consistent (Out := BitVec P.hashBits)
    (In := fun v : Fin S.graph.size => BitVec (S.graph.kind v).inLen)
    (fun v => (S.graph.kind v).input (S.graph.evalRec ξ)) (fun v => ξ.2 v)
  have hpos : (0 : ℝ) < (Fintype.card (BitVec P.hashBits) : ℝ) ^ S.graph.size := by
    have : 0 < Fintype.card (BitVec P.hashBits) := Fintype.card_pos
    positivity
  rw [eq_div_iff hpos.ne', mul_comm]
  have h' : ((Fintype.card (BitVec P.hashBits) ^ S.graph.size * (consTabs S ξ).card : ℕ) : ℝ) =
      (Fintype.card S.graph.Tab : ℕ) := by
    congr 1
    convert h using 3
    ext t
    rw [consTabs, Finset.mem_filter, Finset.mem_filter]
    simp only [Finset.mem_univ, true_and]
    rfl
  exact_mod_cast h'

theorem consTabs_nonempty (ξ : S.graph.Rec) : (consTabs S ξ).Nonempty := by
  exact ⟨fun v _ => ξ.2 v, Finset.mem_filter.2 ⟨Finset.mem_univ _, fun v => rfl⟩⟩

theorem attemptProbNodes_nonneg_le (t : S.graph.Tab) (L : List (Fin S.graph.size))
    (W : Finset S.graph.Rec) : 0 ≤ attemptProbNodes S t L W ∧ attemptProbNodes S t L W ≤ 1 := by
  induction L generalizing W with
  | nil =>
    unfold attemptProbNodes
    split_ifs <;> norm_num
  | cons g L ih =>
    unfold attemptProbNodes
    split_ifs with hW
    · have hc : (0 : ℝ) < (W.card : ℝ) := by exact_mod_cast hW.card_pos
      refine ⟨div_nonneg (Finset.sum_nonneg fun ξ _ => (ih _).1) hc.le, ?_⟩
      rw [div_le_one hc]
      calc _ ≤ ∑ _ξ ∈ W, (1 : ℝ) := Finset.sum_le_sum fun ξ _ => (ih _).2
        _ = _ := by simp
    · norm_num

theorem attemptProbNodes_pos (t : S.graph.Tab) (L : List (Fin S.graph.size))
    (W : Finset S.graph.Rec) (ξ : S.graph.Rec) (hξ : ξ ∈ W) (ht : S.graph.Consistent ξ t) :
    0 < attemptProbNodes S t L W := by
  induction L generalizing W with
  | nil =>
    unfold attemptProbNodes
    rw [if_pos ⟨ξ, hξ⟩]; norm_num
  | cons g L ih =>
    unfold attemptProbNodes
    rw [if_pos ⟨ξ, hξ⟩]
    have hc : (0 : ℝ) < (W.card : ℝ) := by exact_mod_cast Finset.card_pos.2 ⟨ξ, hξ⟩
    refine div_pos (Finset.sum_pos' (fun ξ' _ => (attemptProbNodes_nonneg_le S t L _).1)
      ⟨ξ, hξ, ih _ (Finset.mem_filter.2 ⟨hξ, rfl, (ht g).symm⟩)⟩) hc

theorem input_congr {hb N : ℕ} {len : Fin N → ℕ} {v : Fin N} (k : NodeKind hb N len v)
    (x y : (w : Fin N) → BitVec (len w)) (h : ∀ w ∈ k.parents, x w = y w) :
    k.input x = k.input y := by
  cases k with
  | source => rfl
  | det => rfl
  | hash p _ _ _ =>
    simp only [NodeKind.input]
    exact h p (by simp [NodeKind.parents])

theorem input_evalRec_congr (ξ ξ' : S.graph.Rec) (w g : Fin S.graph.size) (hwg : w ≤ g)
    (h1 : ξ.1 = ξ'.1) (h2 : ∀ v, v < g → ξ.2 v = ξ'.2 v) :
    (S.graph.kind w).input (S.graph.evalRec ξ) = (S.graph.kind w).input (S.graph.evalRec ξ') := by
  refine input_congr _ _ _ fun p hp => ?_
  have hpw := (S.graph.kind w).lt_of_mem_parents hp
  exact S.graph.evalRec_congr ξ ξ' p (fun u _ => by rw [h1])
    (fun u hu => h2 u (lt_of_le_of_lt hu (lt_of_lt_of_le hpw hwg)))

theorem root_mem_evalHashAt (i : Fin P.numSets) : S.graph.root ∈ evalHashAt S i := by
  simp only [evalHashAt, Graph.evalHash, Graph.evaluated, Finset.mem_filter, Finset.mem_univ,
    true_and]
  exact ⟨⟨Graph.Visited.root, S.root_not_mem i⟩, S.graph.root_isHash⟩

theorem mem_obsCands_self (i : Fin P.numSets) (ξ : S.graph.Rec) : ξ ∈ obsCands S i ξ := by
  simp [obsCands, candidates]

theorem obsCands_eq (i : Fin P.numSets) (ξ ξ' : S.graph.Rec) (h : ξ' ∈ obsCands S i ξ) :
    obsCands S i ξ' = obsCands S i ξ := by
  simp only [obsCands, candidates, Finset.mem_filter, Finset.mem_univ, true_and] at h ⊢
  ext ζ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1.trans h.1, fun k hk => (h2 k hk).trans (h.2 k hk)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1.trans h.1.symm, fun k hk => (h2 k hk).trans (h.2 k hk).symm⟩

end Scheme

section Nodes

open Attack

variable {P : Params} (S : Scheme P)

theorem newNodes_nodup (i j : Fin P.numSets) : (newNodes S i j).Nodup :=
  (List.nodup_finRange _).filter _

theorem newNodes_pairwise (i j : Fin P.numSets) : (newNodes S i j).Pairwise (· < ·) :=
  (List.pairwise_lt_finRange _).filter _

theorem mem_newNodes (i j : Fin P.numSets) (g : Fin S.graph.size) :
    g ∈ newNodes S i j ↔ g ∈ evalHashAt S j ∧ g ∉ evalHashAt S i := by
  simp [newNodes]

/-- The `k`-th new node. -/
abbrev nd (i j : Fin P.numSets) (k : Fin (newNodes S i j).length) : Fin S.graph.size :=
  ((newNodes_nodup S i j).getEquiv (newNodes S i j) k).1

/-- Oracle inputs of the `k`-th new node. -/
abbrev nIn (i j : Fin P.numSets) (k : Fin (newNodes S i j).length) : Type :=
  BitVec (S.graph.kind (nd S i j k)).inLen

/-- The input of the `k`-th new node in a record. -/
def nI (i j : Fin P.numSets) : (k : Fin (newNodes S i j).length) → S.graph.Rec → nIn S i j k :=
  fun k ξ => (S.graph.kind (nd S i j k)).input (S.graph.evalRec ξ)

/-- The output of the `k`-th new node in a record. -/
def nY (i j : Fin P.numSets) : Fin (newNodes S i j).length → S.graph.Rec → BitVec P.hashBits :=
  fun k ξ => ξ.2 (nd S i j k)

theorem nd_mem (i j : Fin P.numSets) (k : Fin (newNodes S i j).length) :
    nd S i j k ∈ newNodes S i j :=
  ((newNodes_nodup S i j).getEquiv (newNodes S i j) k).2

theorem nd_lt (i j : Fin P.numSets) {k k' : Fin (newNodes S i j).length} (h : k' < k) :
    nd S i j k' < nd S i j k := by
  have := List.pairwise_iff_getElem.1 (newNodes_pairwise S i j) k' k k'.2 k.2 h
  exact this

theorem attemptProbNodes_eq (i j : Fin P.numSets) (t : S.graph.Tab) (W : Finset S.graph.Rec) :
    attemptProbNodes S t (newNodes S i j) W =
      attemptProb (nI S i j) (nY S i j) W (fun k => t (nd S i j k)) := by
  have gen : ∀ (L : List (Fin (newNodes S i j).length)) (W : Finset S.graph.Rec),
      attemptProbNodes S t (L.map (nd S i j)) W =
        attemptProbList (nI S i j) (nY S i j) (fun k => t (nd S i j k)) L W := by
    intro L
    induction L with
    | nil => intro W; rfl
    | cons k L ih =>
      intro W
      simp only [List.map_cons, attemptProbNodes, attemptProbList]
      simp_rw [ih]
      rfl
  have hmap : (List.finRange (newNodes S i j).length).map (nd S i j) = newNodes S i j := by
    rw [← List.ofFn_eq_map]
    exact List.ofFn_get _
  unfold attemptProb
  rw [← gen, hmap]

/-- Tables on the new nodes consistent with a record. -/
def consOn (i j : Fin P.numSets) (ξ : S.graph.Rec) :
    Finset ((k : Fin (newNodes S i j).length) → nIn S i j k → BitVec P.hashBits) :=
  Finset.univ.filter fun a => ∀ k, a k (nI S i j k ξ) = nY S i j k ξ

theorem avg_consTabs_restrict (i j : Fin P.numSets) (ξ : S.graph.Rec)
    (f : ((k : Fin (newNodes S i j).length) → nIn S i j k → BitVec P.hashBits) → ℝ) :
    (∑ t ∈ consTabs S ξ, f (fun k => t (nd S i j k))) / ((consTabs S ξ).card : ℝ) =
      (∑ a ∈ consOn S i j ξ, f a) / ((consOn S i j ξ).card : ℝ) := by
  exact AvgSuccAux.avg_restrict (β := fun v : Fin S.graph.size =>
      BitVec (S.graph.kind v).inLen → BitVec P.hashBits)
    (fun v => v ∈ newNodes S i j) ((newNodes_nodup S i j).getEquiv (newNodes S i j))
    (fun v x => x ((S.graph.kind v).input (S.graph.evalRec ξ)) = ξ.2 v)
    (fun v => ⟨fun _ => ξ.2 v, rfl⟩) f _
    (fun t => by rw [consTabs, Finset.mem_filter]; simp only [Finset.mem_univ, true_and]; rfl) _
    (fun a => by rw [consOn, Finset.mem_filter]; simp only [Finset.mem_univ, true_and]; rfl)

theorem card_consOn (i j : Fin P.numSets) (ξ : S.graph.Rec) :
    ((consOn S i j ξ).card : ℝ) =
      (Fintype.card ((k : Fin (newNodes S i j).length) → nIn S i j k → BitVec P.hashBits) : ℝ) /
        (Fintype.card (BitVec P.hashBits) : ℝ) ^ (newNodes S i j).length := by
  have h := card_tables_consistent (Out := BitVec P.hashBits) (In := nIn S i j)
    (fun k => nI S i j k ξ) (fun k => nY S i j k ξ)
  have hpos : (0 : ℝ) < (Fintype.card (BitVec P.hashBits) : ℝ) ^ (newNodes S i j).length := by
    have : 0 < Fintype.card (BitVec P.hashBits) := Fintype.card_pos
    positivity
  rw [eq_div_iff hpos.ne', mul_comm]
  have h' : ((Fintype.card (BitVec P.hashBits) ^ (newNodes S i j).length *
      (consOn S i j ξ).card : ℕ) : ℝ) =
      (Fintype.card ((k : Fin (newNodes S i j).length) → nIn S i j k → BitVec P.hashBits) : ℕ) := by
    congr 1
  exact_mod_cast h'

theorem condEntropy_weight_le_trace (i j : Fin P.numSets) (C : Finset S.graph.Rec)
    (k : Fin (newNodes S i j).length) :
    condEntropy C (nY S i j k) (fun ξ => (ξ.1, outputsBefore ξ.2 (nd S i j k))) ≤
      condEntropy C (nY S i j k)
        (fun ξ => (traceBefore (nI S i j) (nY S i j) k ξ, nI S i j k ξ)) := by
  let hat : S.graph.Assignment × (Fin S.graph.size → Option (BitVec P.hashBits)) → S.graph.Rec :=
    fun zo => (zo.1, fun v => (zo.2 v).getD 0)
  refine condEntropy_le_of_factor C (nY S i j k) _ _
    (fun zo => (traceBefore (nI S i j) (nY S i j) k (hat zo), nI S i j k (hat zo)))
    fun ξ _ => ?_
  set ξ' := hat (ξ.1, outputsBefore ξ.2 (nd S i j k)) with hξ'
  have h1 : ξ.1 = ξ'.1 := rfl
  have h2 : ∀ v, v < nd S i j k → ξ.2 v = ξ'.2 v := by
    intro v hv
    show ξ.2 v = (outputsBefore ξ.2 (nd S i j k) v).getD 0
    rw [outputsBefore, if_pos hv]
    rfl
  refine Prod.ext ?_ ?_
  · funext k'
    simp only [traceBefore]
    split_ifs with hk'
    · have hlt := nd_lt S i j hk'
      rw [show nI S i j k' ξ = nI S i j k' ξ' from
        input_evalRec_congr S ξ ξ' _ _ hlt.le h1 h2]
      rw [show nY S i j k' ξ = nY S i j k' ξ' from h2 _ hlt]
    · rfl
  · exact input_evalRec_congr S ξ ξ' _ _ le_rfl h1 h2

theorem sum_weight_nd_le (i j : Fin P.numSets) (C : Finset S.graph.Rec) :
    ∑ k, weight S i C (nd S i j k) ≤ targetWeight S i C j := by
  have e1 : ∑ k, weight S i C (nd S i j k) =
      ∑ x : {v // v ∈ newNodes S i j}, weight S i C x.1 :=
    Equiv.sum_comp ((newNodes_nodup S i j).getEquiv (newNodes S i j)) (fun x => weight S i C x.1)
  rw [e1, ← Finset.sum_subtype (newNodes S i j).toFinset (fun _ => List.mem_toFinset)]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun g _ _ => weight_nonneg' S i C g
  intro g hg
  rw [List.mem_toFinset, mem_newNodes] at hg
  refine Finset.mem_erase.2 ⟨?_, hg.1⟩
  rintro rfl
  exact hg.2 (root_mem_evalHashAt S i)

theorem avg_neg_logb_le (i j : Fin P.numSets) (C : Finset S.graph.Rec) (hC : C.Nonempty) :
    (∑ ξ ∈ C, (∑ t ∈ consTabs S ξ, -Real.logb 2 (attemptProbNodes S t (newNodes S i j) C)) /
        ((consTabs S ξ).card : ℝ)) / (C.card : ℝ) ≤ targetWeight S i C j := by
  have hc := sum_neg_logb_attemptProb_le (nI S i j) (nY S i j) C hC
  dsimp only at hc
  set κ := (Fintype.card ((k : Fin (newNodes S i j).length) → nIn S i j k → BitVec P.hashBits) : ℝ) /
    (Fintype.card (BitVec P.hashBits) : ℝ) ^ (newNodes S i j).length with hκ
  have hκpos : 0 < κ := by
    rw [hκ, ← card_consOn S i j hC.choose]
    exact_mod_cast Finset.card_pos.2 ⟨fun k _ => nY S i j k hC.choose,
      Finset.mem_filter.2 ⟨Finset.mem_univ _, fun k => rfl⟩⟩
  have hsumP : ∀ g : S.graph.Rec × ((k : Fin (newNodes S i j).length) → nIn S i j k →
      BitVec P.hashBits) → ℝ,
      ∑ q ∈ (C ×ˢ Finset.univ).filter (fun p : S.graph.Rec × ((k : Fin (newNodes S i j).length) →
        nIn S i j k → BitVec P.hashBits) => ∀ k, p.2 k (nI S i j k p.1) = nY S i j k p.1), g q =
      ∑ ξ ∈ C, ∑ a ∈ consOn S i j ξ, g (ξ, a) := by
    intro g
    rw [Finset.sum_filter, Finset.sum_product]
    refine Finset.sum_congr rfl fun ξ _ => ?_
    rw [consOn, Finset.sum_filter]
  have hcardP : (((C ×ˢ Finset.univ).filter (fun p : S.graph.Rec × ((k : Fin (newNodes S i j).length) →
        nIn S i j k → BitVec P.hashBits) => ∀ k, p.2 k (nI S i j k p.1) = nY S i j k p.1)).card : ℝ) =
      C.card * κ := by
    rw [Finset.card_eq_sum_ones, Nat.cast_sum, hsumP]
    simp only [Nat.cast_one, Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [Finset.sum_congr rfl fun ξ _ => card_consOn S i j ξ, Finset.sum_const, nsmul_eq_mul]
  have hL : (∑ ξ ∈ C, (∑ t ∈ consTabs S ξ, -Real.logb 2 (attemptProbNodes S t (newNodes S i j) C)) /
        ((consTabs S ξ).card : ℝ)) / (C.card : ℝ) =
      (∑ q ∈ (C ×ˢ Finset.univ).filter (fun p : S.graph.Rec × ((k : Fin (newNodes S i j).length) →
        nIn S i j k → BitVec P.hashBits) => ∀ k, p.2 k (nI S i j k p.1) = nY S i j k p.1),
          -Real.logb 2 (attemptProb (nI S i j) (nY S i j) C q.2)) /
      (((C ×ˢ Finset.univ).filter (fun p : S.graph.Rec × ((k : Fin (newNodes S i j).length) →
        nIn S i j k → BitVec P.hashBits) => ∀ k, p.2 k (nI S i j k p.1) = nY S i j k p.1)).card : ℝ) := by
    rw [hcardP, hsumP]
    simp_rw [attemptProbNodes_eq S i j _ C]
    rw [Finset.sum_congr rfl fun ξ _ => avg_consTabs_restrict S i j ξ
      (fun a => -Real.logb 2 (attemptProb (nI S i j) (nY S i j) C a))]
    simp_rw [card_consOn S i j, ← hκ, ← Finset.sum_div]
    rw [div_div, mul_comm κ]
  rw [hL]
  refine hc.trans ?_
  refine le_trans (Finset.sum_le_sum fun k _ => ?_) (sum_weight_nd_le S i j C)
  have hk : nd S i j k ∉ evalHashAt S i := ((mem_newNodes S i j _).1 (nd_mem S i j k)).2
  have := condEntropy_weight_le_trace S i j C k
  unfold weight
  rw [if_neg hk]
  exact sub_le_sub_left this _

end Nodes

section Core

open Attack

variable {P : Params} (S : Scheme P)

/-- Success probability of the forging step for a candidate set `C`. -/
def succC (i : Fin P.numSets) (ℓ : ℕ) (C : Finset S.graph.Rec) (t : S.graph.Tab) : ℝ :=
  if rankElem S i C ℓ = i then 1 else
    1 - (1 - attemptProbNodes S t (newNodes S i (rankElem S i C ℓ)) C) ^ Numerics.q

omit S in
theorem pow_le_neg_logb_div (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) :
    (1 - p) ^ Numerics.q ≤ -Real.logb 2 p / 113 := by
  have hq3 : 3 ≤ Numerics.q := by unfold Numerics.q; norm_num
  have h := one_sub_pow_le_neg_log_div Numerics.q hq3 p hp hp1
  have hb := Numerics.budget_lt_logb
  have hqR : (3 : ℝ) ≤ Numerics.q := by exact_mod_cast hq3
  have hlq1 : 1 < Real.log Numerics.q := by
    rw [Real.lt_log_iff_exp_lt (by linarith)]
    have := Real.exp_one_lt_d9; linarith
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have heq : Real.logb 2 (Real.exp 1 * Numerics.q * Real.log Numerics.q) * Real.log 2 =
      Real.log Numerics.q + Real.log (Real.log Numerics.q) + 1 := by
    rw [Real.logb, div_mul_cancel₀ _ hl2.ne', Real.log_mul (by positivity) (ne_of_gt (by linarith)),
      Real.log_mul (by positivity) (by positivity), Real.log_exp]
    ring
  have hu : 0 ≤ -Real.log p := by have := Real.log_nonpos hp.le hp1; linarith
  refine h.trans ?_
  have e : -Real.logb 2 p / 113 = -Real.log p / (113 * Real.log 2) := by
    rw [Real.logb]; ring
  rw [← heq, e]
  exact div_le_div_of_nonneg_left hu (by positivity) (mul_le_mul_of_nonneg_right hb.le hl2.le)

theorem core (i : Fin P.numSets) (ℓ : ℕ) (C : Finset S.graph.Rec) (hC : C.Nonempty) :
    max 0 (1 - targetWeight S i C (rankElem S i C ℓ) / 113) ≤
      (∑ ξ ∈ C, (∑ t ∈ consTabs S ξ, succC S i ℓ C t) / ((consTabs S ξ).card : ℝ)) /
        (C.card : ℝ) := by
  have hCc : (0 : ℝ) < C.card := by exact_mod_cast hC.card_pos
  have hT : ∀ ξ, (0 : ℝ) < (consTabs S ξ).card := fun ξ => by
    exact_mod_cast (consTabs_nonempty S ξ).card_pos
  have hw := targetWeight_nonneg' S i C (rankElem S i C ℓ)
  by_cases hj : rankElem S i C ℓ = i
  · have h1 : ∀ t, succC S i ℓ C t = 1 := fun t => by simp only [succC, if_pos hj]
    simp only [h1, Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [Finset.sum_congr rfl fun ξ _ => div_self (hT ξ).ne', Finset.sum_const, nsmul_eq_mul,
      mul_one, div_self hCc.ne']
    exact max_le zero_le_one (by linarith [div_nonneg hw (by norm_num : (0 : ℝ) ≤ 113)])
  · have hs : ∀ t, succC S i ℓ C t =
        1 - (1 - attemptProbNodes S t (newNodes S i (rankElem S i C ℓ)) C) ^ Numerics.q :=
      fun t => by simp only [succC, if_neg hj]
    simp only [hs]
    generalize rankElem S i C ℓ = j
    apply max_le
    · refine div_nonneg (Finset.sum_nonneg fun ξ _ =>
        div_nonneg (Finset.sum_nonneg fun t _ => ?_) (hT ξ).le) hCc.le
      obtain ⟨h0, h1⟩ := attemptProbNodes_nonneg_le S t (newNodes S i j) C
      have : (1 - attemptProbNodes S t (newNodes S i j) C) ^ Numerics.q ≤ 1 :=
        pow_le_one₀ (by linarith) (by linarith)
      linarith
    · have hkey := avg_neg_logb_le S i j C hC
      have hpt : ∀ ξ ∈ C, 1 - ((∑ t ∈ consTabs S ξ,
            -Real.logb 2 (attemptProbNodes S t (newNodes S i j) C)) /
            ((consTabs S ξ).card : ℝ)) / 113 ≤
          (∑ t ∈ consTabs S ξ, (1 - (1 - attemptProbNodes S t (newNodes S i j) C) ^ Numerics.q)) /
            ((consTabs S ξ).card : ℝ) := by
        intro ξ hξ
        have e : 1 - ((∑ t ∈ consTabs S ξ,
              -Real.logb 2 (attemptProbNodes S t (newNodes S i j) C)) /
              ((consTabs S ξ).card : ℝ)) / 113 =
            (∑ t ∈ consTabs S ξ, (1 - -Real.logb 2 (attemptProbNodes S t (newNodes S i j) C) / 113)) /
              ((consTabs S ξ).card : ℝ) := by
          have hne := (hT ξ).ne'
          rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one, ← Finset.sum_div]
          field_simp
        rw [e]
        refine div_le_div_of_nonneg_right (Finset.sum_le_sum fun t ht => ?_) (hT ξ).le
        have hcons : S.graph.Consistent ξ t := (Finset.mem_filter.1 ht).2
        have hp := attemptProbNodes_pos S t (newNodes S i j) C ξ hξ hcons
        have hp1 := (attemptProbNodes_nonneg_le S t (newNodes S i j) C).2
        linarith [pow_le_neg_logb_div _ hp hp1]
      calc 1 - targetWeight S i C j / 113
          ≤ 1 - ((∑ ξ ∈ C, (∑ t ∈ consTabs S ξ,
              -Real.logb 2 (attemptProbNodes S t (newNodes S i j) C)) /
              ((consTabs S ξ).card : ℝ)) / (C.card : ℝ)) / 113 := by
            linarith [div_le_div_of_nonneg_right hkey (by norm_num : (0 : ℝ) ≤ 113)]
        _ = (∑ ξ ∈ C, (1 - ((∑ t ∈ consTabs S ξ,
              -Real.logb 2 (attemptProbNodes S t (newNodes S i j) C)) /
              ((consTabs S ξ).card : ℝ)) / 113)) / (C.card : ℝ) := by
            rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one, ← Finset.sum_div]
            field_simp
        _ ≤ _ := div_le_div_of_nonneg_right (Finset.sum_le_sum hpt) hCc.le

end Core

end AvgSuccAux

open AvgSuccAux in
theorem avg_D_le_avg_succ (S : Scheme paperParams) (i : Fin paperParams.numSets) (ℓ : ℕ) :
    (∑ ξ : S.graph.Rec, max 0 (1 - D S i ℓ ξ / 113)) / (Fintype.card S.graph.Rec : ℝ) ≤
      (∑ z : S.graph.Assignment, ∑ t : S.graph.Tab, succ S Numerics.q i ℓ z t) /
        ((Fintype.card S.graph.Assignment : ℝ) * Fintype.card S.graph.Tab) := by
  set R : S.graph.Rec → ℝ := fun ξ =>
    (∑ t ∈ consTabs S ξ, succC S i ℓ (obsCands S i ξ) t) / ((consTabs S ξ).card : ℝ) with hR
  set κ := (Fintype.card S.graph.Tab : ℝ) /
    (Fintype.card (BitVec paperParams.hashBits) : ℝ) ^ S.graph.size with hκ
  have hT : ∀ ξ, (0 : ℝ) < (consTabs S ξ).card := fun ξ => by
    exact_mod_cast (AvgSuccAux.consTabs_nonempty S ξ).card_pos
  have hκpos : 0 < κ := by
    rw [hκ, ← AvgSuccAux.card_consTabs S (fun _ => 0, fun _ => 0)]
    exact hT _
  have hnum : ∑ z : S.graph.Assignment, ∑ t : S.graph.Tab, succ S Numerics.q i ℓ z t =
      κ * ∑ ξ, R ξ := by
    refine (AvgSuccAux.sum_recOf S (fun ξ t => AvgSuccAux.succC S i ℓ (obsCands S i ξ) t)).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun ξ _ => ?_
    have hne := (hT ξ).ne'
    rw [hR, hκ, ← AvgSuccAux.card_consTabs S ξ]
    field_simp
  have hden : (Fintype.card S.graph.Assignment : ℝ) * Fintype.card S.graph.Tab =
      Fintype.card S.graph.Rec * κ := by
    have hpos : (0 : ℝ) < (Fintype.card (BitVec paperParams.hashBits) : ℝ) ^ S.graph.size := by
      have : 0 < Fintype.card (BitVec paperParams.hashBits) := Fintype.card_pos
      positivity
    rw [hκ, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin]
    push_cast
    field_simp
  have hclass := AvgSuccAux.sum_eq_sum_class_avg (obsCands S i) (AvgSuccAux.mem_obsCands_self S i)
    (AvgSuccAux.obsCands_eq S i) R
  rw [hnum, hden, mul_comm (Fintype.card S.graph.Rec : ℝ) κ, mul_div_mul_left _ _ hκpos.ne', hclass]
  refine div_le_div_of_nonneg_right (Finset.sum_le_sum fun ξ _ => ?_) (Nat.cast_nonneg _)
  have e : ∑ ξ' ∈ obsCands S i ξ, R ξ' = ∑ ξ' ∈ obsCands S i ξ,
      (∑ t ∈ consTabs S ξ', AvgSuccAux.succC S i ℓ (obsCands S i ξ) t) /
        ((consTabs S ξ').card : ℝ) := by
    refine Finset.sum_congr rfl fun ξ' hξ' => ?_
    rw [hR]
    dsimp only
    rw [AvgSuccAux.obsCands_eq S i ξ ξ' hξ']
  rw [e]
  exact AvgSuccAux.core S i ℓ (obsCands S i ξ) ⟨ξ, AvgSuccAux.mem_obsCands_self S i ξ⟩

end Analysis

end OptimalOTS
