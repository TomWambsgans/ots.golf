import Submissions.DisclosureLower.Conversion
import Submissions.DisclosureLower.Patterns
import Submissions.DisclosureLower.PatternSearch
import Submissions.DisclosureLower.CostCore
import Submissions.DisclosureLower.PatternHelpers

/-! A forgery attack using equal reconstruction patterns. -/

open OracleSpec OracleComp OracleComp.EvalDist ENNReal
noncomputable section
open scoped Classical

namespace OptimalOTS.PatternAttack

variable {P : Params} (S : Scheme P)

def targets (i : Fin P.numSets) : Finset ℕ := (S.samePattern i).image Fin.val

def fallback (m : Message P) : Message P × Signature P :=
  (m, 0, List.replicate (P.maxRevealBits + 1) false)

def fromResult (i : Fin P.numSets) (xa xr : S.graph.Assignment) (m : Message P) :
    Option (Nonce P × ℕ) → Message P × Signature P
  | none => fallback m
  | some (η, n) =>
      if hn : n < P.numSets then
        (m, η, Conversion.convert S i ⟨n, hn⟩ xa xr)
      else fallback m

def forgeFrom (T : ℕ) (i : Fin P.numSets) (xa xr : S.graph.Assignment)
    (m₁ : Message P) : OracleComp (Spec P) (Message P × Signature P) := do
  let m₂ ← sampleBits P P.msgBits
  if m₂ = m₁ then pure (fallback m₁) else
    fromResult S i xa xr m₂ <$> PatternSearch.search P (targets S i) m₂ T 0

def forge (T : ℕ) (m₁ : Message P) :
    Option (Signature P) → OracleComp (Spec P) (Message P × Signature P)
  | none => pure (fallback m₁)
  | some (η₁, pl) => do
      let n ← index P m₁ η₁
      if hn : n < P.numSets then
        let i : Fin P.numSets := ⟨n, hn⟩
        let xa := S.graph.decode (S.sets i) pl
        let xr ← S.graph.reconstruct (S.sets i) xa
        forgeFrom S T i xa xr m₁
      else pure (fallback m₁)

def adversary (T : ℕ) : Adversary P where
  State := Message P
  choose _ := (fun m => (m,m)) <$> sampleBits P P.msgBits
  forge := forge S T

/-- The final weak-security check after a signature was returned. -/
def check (pk : PublicKey P) (m₁ : Message P) (out : Message P × Signature P) :
    OracleComp (Spec P) Bool := do
  let ok ← S.verify pk out.1 out.2
  return ok && decide (out.1 ≠ m₁)

def win (p : Bool × Cache P) : ℝ≥0∞ := if p.1 = true then 1 else 0

theorem mem_targets (i : Fin P.numSets) (n : ℕ) (hn : n ∈ targets S i) :
    ∃ j : Fin P.numSets, j.val = n ∧ S.graph.evalHash (S.sets j) = S.graph.evalHash (S.sets i) := by
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hn
  refine ⟨j,rfl, (S.hashPattern_eq_iff j i).mp ?_⟩
  exact (Finset.mem_filter.mp hj).2

theorem card_targets (i : Fin P.numSets) : (targets S i).card = (S.samePattern i).card :=
  Finset.card_image_of_injective _ Fin.val_injective

/-- A successful target search supplies a cache entry and an equal reconstruction pattern. -/
theorem check_fromResult (i : Fin P.numSets) (x : S.graph.Assignment)
    (m₁ m₂ : Message P) (hne : m₂ ≠ m₁) (c : Cache P)
    (hc : S.graph.CacheConsistent x c) (η : Nonce P) (n : ℕ) (hn : n ∈ targets S i)
    (w : BitVec P.hashBits) (hw : c ⟨P.msgBits + P.nonceBits,m₂ ++ η⟩ = some w)
    (hidx : (w.setWidth P.idxBits).toNat = n) :
    run P (check S (S.publicKey x) m₁ (fromResult S i
      (S.graph.decode (S.sets i) (S.graph.encode (S.sets i) x))
      (Conversion.observed S i x) m₂ (some (η,n)))) c = pure (true,c) := by
  obtain ⟨j,rfl,hj⟩ := mem_targets S i n hn
  simp only [fromResult, dif_pos j.isLt, Fin.eta, check]
  rw [run_bind, Conversion.run_verify_convert_cached S i j x m₂ η c hc
    (by rw [Conversion.evalHashAt, Conversion.evalHashAt, hj]) w hw hidx, pure_bind, run_pure]
  have he : decide (m₂ ≠ m₁) = true := decide_eq_true hne
  rw [he]
  rfl

/-! Query costs. -/

theorem cost_forgeFrom (T : ℕ) (i : Fin P.numSets) (xa xr : S.graph.Assignment)
    (m₁ : Message P) (hidx : blockCost P (P.msgBits + P.nonceBits) = 1) :
    CostAtMost P (forgeFrom S T i xa xr m₁) T := by
  unfold forgeFrom
  refine (costAtMost_liftM_probComp _ 0).bind_le (b₂ := T) (fun m₂ => ?_) (by simp)
  split_ifs
  · exact costAtMost_pure _ _
  · exact (PatternSearch.cost_search hidx (targets S i) m₂ T 0).map _

theorem cost_forge (T : ℕ) (hidx : blockCost P (P.msgBits + P.nonceBits) = 1)
    {v : ℕ} (hv : ∀ i, S.graph.reconstructCost (S.sets i) ≤ v) (m₁ : Message P) :
    ∀ σ, CostAtMost P (forge S T m₁ σ) (1 + v + T)
  | none => costAtMost_pure _ _
  | some (η, pl) => by
    unfold forge
    refine (costAtMost_index hidx _ _).bind_le (b₂ := v + T) (fun n => ?_) (by omega)
    split_ifs with hn
    · refine ((S.graph.costAtMost_reconstruct _ _).mono (hv ⟨n,hn⟩)).bind
        (fun xr => cost_forgeFrom S T ⟨n,hn⟩ _ xr m₁ hidx)
    · exact costAtMost_pure _ _

theorem cost_experiment (T v : ℕ)
    (hidx : blockCost P (P.msgBits + P.nonceBits) = 1)
    (hv : ∀ i, S.graph.reconstructCost (S.sets i) ≤ v) :
    CostAtMost P (weakExperiment S (adversary S T))
      (P.keygenBudget + P.trialLimit + T + 2*v + 2) := by
  unfold weakExperiment
  refine S.costAtMost_keygen.bind_le
    (b₂ := P.trialLimit + (1+v+T) + (1+v)) (fun kg => ?_) (by omega)
  refine ((costAtMost_liftM_probComp _ 0).map _).bind_le
    (b₂ := P.trialLimit + (1+v+T) + (1+v)) (fun st => ?_) (by simp)
  refine (S.costAtMost_sign hidx kg.2 st.1).bind_le
    (b₂ := (1+v+T) + (1+v)) (fun σ => ?_) (by omega)
  refine (cost_forge S T hidx hv st.2 σ).bind (fun out => ?_)
  exact (S.costAtMost_verify hidx hv kg.1 out.1 out.2).bind_le
    (fun _ => costAtMost_pure _ 0) (by simp)

/-! Success after receiving an honest signature in a large pattern class. -/

theorem search_check_ge (T : ℕ) (i : Fin P.numSets) (x : S.graph.Assignment)
    (m₁ m₂ : Message P) (hne : m₂ ≠ m₁) (c : Cache P)
    (hc : S.graph.CacheConsistent x c) :
    E (run P (PatternSearch.search P (targets S i) m₂ T 0) c)
      (fun p => if p.1.isSome then 1 else 0) ≤
    E (run P (PatternSearch.search P (targets S i) m₂ T 0) c) (fun p =>
      E (run P (check S (S.publicKey x) m₁ (fromResult S i
        (S.graph.decode (S.sets i) (S.graph.encode (S.sets i) x))
        (Conversion.observed S i x) m₂ p.1)) p.2) win) := by
  apply expectedValue_mono_of_support
  intro p hp
  rcases he : p.1 with _ | ⟨η,n⟩
  · simp [he]
  · obtain ⟨hn,w,hw,hidx⟩ := PatternSearch.search_support (targets S i) m₂ T 0 c p hp η n he
    have hc' := Graph.CacheConsistent.mono S.graph
      (sub_of_mem_support_run P _ c p hp) hc
    rw [check_fromResult S i x m₁ m₂ hne p.2 hc' η n hn w hw hidx, E_pure]
    simp [win]

theorem forgeFrom_success_ge (S : Scheme paperParams) (i : Fin paperParams.numSets)
    (x : S.graph.Assignment) (c : Cache paperParams)
    (hc : S.graph.CacheConsistent x c) (hclass : 8 ≤ (S.samePattern i).card)
    (D : Finset Query) (hD : BareLower.HasSupport c D) (hcardD : D.card ≤ 2 ^ 22)
    (m₁ : Message paperParams) :
    (1 / 10 : ℝ≥0∞) ≤ E (run paperParams
      (forgeFrom S (2 ^ 122) i
        (S.graph.decode (S.sets i) (S.graph.encode (S.sets i) x))
        (Conversion.observed S i x) m₁ >>= check S (S.publicKey x) m₁) c) win := by
  unfold forgeFrom
  rw [bind_assoc, run_bind, E_bind, sampleBits, run_liftM, E_map]
  have hmass := BareLower.fresh_new_mass_paper hD hcardD m₁
  refine le_trans ?_ (BareLower.expectedValue_ge_indicator ($ᵗ BitVec paperParams.msgBits)
    (fun m₂ => BareLower.FreshMessage c m₂ ∧ m₂ ≠ m₁) _ (1 / 9) ?_)
  · have he : (1 / 10 : ℝ≥0∞) = (9 / 10) * (1 / 9) := by
      symm
      rw [div_eq_mul_inv, one_div, mul_right_comm,
        ENNReal.mul_inv_cancel (by norm_num : (9 : ℝ≥0∞) ≠ 0) (by norm_num), one_mul,
        one_div]
    rw [he]
    refine (mul_le_mul_left hmass (1 / 9)).trans ?_
    apply mul_le_mul_left
    apply E_mono
    intro m
    split_ifs <;> simp_all
  · intro m₂ _ hm₂
    dsimp only
    rw [if_neg hm₂.2, bind_map_left, run_bind, E_bind]
    apply (PatternSearch.paper_success_ge (targets S i) (fun n hn => ?_)
      (by rw [card_targets]; exact hclass) m₂ c hm₂.1).trans
    · exact search_check_ge S _ i x m₁ m₂ hm₂.2 c hc
    · obtain ⟨j,rfl,_⟩ := mem_targets S i n hn
      have hj := j.isLt
      change j.val < 2 ^ 115 at hj
      exact hj.trans (by norm_num)

theorem forge_success_ge (S : Scheme paperParams) (i : Fin paperParams.numSets)
    (x : S.graph.Assignment) (c : Cache paperParams)
    (hc : S.graph.CacheConsistent x c) (hclass : 8 ≤ (S.samePattern i).card)
    (D : Finset Query) (hD : BareLower.HasSupport c D) (hcardD : D.card ≤ 2 ^ 22)
    (m₁ : Message paperParams) (η₁ : Nonce paperParams)
    (w : BitVec paperParams.hashBits)
    (hw : c ⟨paperParams.msgBits + paperParams.nonceBits,m₁ ++ η₁⟩ = some w)
    (hidx : (w.setWidth paperParams.idxBits).toNat = i.val) :
    (1 / 10 : ℝ≥0∞) ≤ E (run paperParams
      (forge S (2 ^ 122) m₁ (some (η₁,S.graph.encode (S.sets i) x)) >>=
        check S (S.publicKey x) m₁) c) win := by
  unfold forge
  rw [bind_assoc, run_bind, Conversion.run_index_cached m₁ η₁ c w hw, E_bind, E_pure]
  dsimp only
  generalize (w.setWidth paperParams.idxBits).toNat = n at hidx ⊢
  subst hidx
  rw [dif_pos i.isLt]
  simp only [Fin.eta, bind_assoc]
  rw [run_bind, Conversion.run_honest_reconstruct S i x c hc, E_bind, E_pure]
  exact forgeFrom_success_ge S i x c hc hclass D hD hcardD m₁

end OptimalOTS.PatternAttack
