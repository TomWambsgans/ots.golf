import Submissions.Upper.Tree
import Submissions.Upper.Keygen

/-!
# Values of the concrete scheme

For a record `ξ : Rec` (sources and hash outputs), `val ξ n` is the value of node `n` in the
honest evaluation `graph.evalRec ξ`.  This file gives the explicit formulas (`val_src`, …,
`val_rh`), describes the keygen cache (`kc ξ`) through the keygen points `pointOf ξ h p` of the
hash nodes, splits it into the exposed and hidden parts relative to a disclosure set
(`fExp`, `fHid`), defines the event `Spr` (a cached answer at a non-keygen point that begins with
an honest value), and records which record coordinates each value depends on (`deps`), with the
two coordinate updates `updSrc` and `updHash`.
-/

open OracleSpec OracleComp ENNReal

noncomputable section

open scoped Classical

namespace OptimalOTS

namespace Flat

open Name

/-- Records of the concrete graph. -/
abbrev Rec := graph.Rec

/-- The value of node `n` in the record `ξ`. -/
def val (ξ : Rec) (n : Name) : BitVec n.len := (graph.evalRec ξ n.fin).cast (graph_len_fin n)

/-! ### Auxiliary cast lemmas -/

theorem trunc_cast {n m : ℕ} (h : n = m) (x : BitVec n) : trunc (x.cast h) = trunc x := by
  subst h; rfl

theorem trunc_trunc {n : ℕ} (x : BitVec n) : trunc (trunc x) = trunc x := BitVec.setWidth_eq _

theorem cast_cast_eq {n m : ℕ} (h₁ : n = m) (h₂ : m = n) (x : BitVec n) :
    (x.cast h₁).cast h₂ = x := by
  subst h₁; rfl

theorem cast_heq_self {n m : ℕ} (h : n = m) (x : BitVec n) : HEq (x.cast h) x := by
  subst h; rfl

/-- The node equation of the concrete graph, with the kind computed by `kindOf`. -/
theorem evalRec_apply_fin (ξ : Rec) (n : Name) :
    graph.evalRec ξ n.fin =
      (kindOf n.fin n (ofFin_fin n)).value (graph.evalRec ξ) (ξ.1 n.fin) (ξ.2 n.fin) := by
  have := Graph.evalRec_apply graph ξ n.fin
  rwa [graph_kind_fin] at this

theorem trunc_evalRec (ξ : Rec) (n : Name) : trunc (graph.evalRec ξ n.fin) = trunc (val ξ n) := by
  unfold val
  exact (trunc_cast _ _).symm

theorem val_src (ξ : Rec) (k : Fin 41) : val ξ (src k) = (ξ.1 (src k).fin).cast (graph_len_fin _) := by
  unfold val
  rw [evalRec_apply_fin]
  rfl

theorem val_ch (ξ : Rec) (k : Fin 41) (t : Fin 20) : val ξ (ch k t) = ξ.2 (ch k t).fin := by
  unfold val
  rw [evalRec_apply_fin]
  simp only [kindOf, NodeKind.value]
  exact cast_cast_eq _ _ _

theorem trunc_val_ch (ξ : Rec) (k : Fin 41) (t : Fin 20) :
    trunc (graph.evalRec ξ (ch k t).fin) = trunc (ξ.2 (ch k t).fin) := by
  rw [trunc_evalRec, val_ch]
  rfl

theorem val_cv (ξ : Rec) (k : Fin 41) (t : Fin 20) : val ξ (cv k t) = trunc (ξ.2 (ch k t).fin) := by
  unfold val
  rw [evalRec_apply_fin]
  simp only [kindOf, NodeKind.value]
  refine (cast_cast_eq _ _ _).trans ?_
  show trunc (graph.evalRec ξ (ch k t).fin) = _
  exact trunc_val_ch ξ k t

theorem trunc_val_cv (ξ : Rec) (k : Fin 41) (t : Fin 20) :
    trunc (graph.evalRec ξ (cv k t).fin) = trunc (ξ.2 (ch k t).fin) := by
  rw [trunc_evalRec, val_cv]
  exact trunc_trunc _

theorem val_rc (ξ : Rec) : val ξ rc = cat41 fun k => trunc (ξ.2 (ch k 19).fin) := by
  unfold val
  rw [evalRec_apply_fin]
  simp only [kindOf, NodeKind.value]
  refine (cast_cast_eq _ _ _).trans ?_
  show cat41 (fun k => trunc (graph.evalRec ξ (cv k 19).fin)) = _
  exact congrArg cat41 (funext fun k => trunc_val_cv ξ k 19)

theorem val_rh (ξ : Rec) : val ξ rh = ξ.2 rh.fin := by
  unfold val
  rw [evalRec_apply_fin]
  simp only [kindOf, NodeKind.value]
  exact cast_cast_eq _ _ _

/-- The public key of a record: the first 128 bits of the root. -/
def pkOf (ξ : Rec) : BitVec 128 := trunc (ξ.2 rh.fin)

/-! ## Hash nodes and keygen points -/

/-- The node whose value a hash node hashes. -/
def hashParent : Name → Option Name
  | ch k t => some (prev k t)
  | rh => some rc
  | _ => none

theorem hashParent_isSome_iff (h : Name) : (hashParent h).isSome ↔ h.cost ≠ 0 := by
  cases h <;> simp [hashParent, Name.cost]

theorem child_hashParent {h p : Name} (hp : hashParent h = some p) : child p = some h := by
  cases h <;> simp only [hashParent, Option.some.injEq, reduceCtorEq] at hp <;> subst hp
  · unfold Name.prev
    split_ifs with ht
    · simp only [Name.child, Option.some.injEq, Name.ch.injEq, true_and, Fin.ext_iff, Fin.val_zero]
      omega
    · simp only [Name.child]
      rw [dif_neg (by omega)]
      simp only [Option.some.injEq, Name.ch.injEq, true_and, Fin.ext_iff]
      omega
  all_goals rfl

theorem len_hashParent {h p : Name} (hp : hashParent h = some p) : 128 ≤ p.len := by
  cases h <;> simp only [hashParent, Option.some.injEq, reduceCtorEq] at hp <;> subst hp
  · rw [Name.len_prev]
  all_goals norm_num [Name.len]

/-- The keygen point of the hash node `h` with parent `p`. -/
def pointOf (ξ : Rec) (h p : Name) : Query := (.node h.idx, ⟨p.len, val ξ p⟩)

theorem pointOf_inj_left {ξ ξ' : Rec} {h h' p p' : Name} (e : pointOf ξ h p = pointOf ξ' h' p') :
    h = h' := by
  have := congrArg Prod.fst e
  simp only [pointOf, Label.node.injEq] at this
  exact Name.idx_injective this

theorem pointOf_inj_input {ξ ξ' : Rec} {h p : Name} (e : pointOf ξ h p = pointOf ξ' h p) :
    val ξ p = val ξ' p := by
  have := congrArg Prod.snd e
  simp only [pointOf, Sigma.mk.inj_iff, heq_eq_eq, true_and] at this
  exact this

theorem sigma_mk_cast_eq {n m : ℕ} (h : n = m) (x : BitVec n) :
    (⟨n, x⟩ : Σ k, BitVec k) = ⟨m, x.cast h⟩ := by
  subst h; rfl

theorem sigma_val (ξ : Rec) (p : Name) :
    (⟨lenF p.fin, graph.evalRec ξ p.fin⟩ : Σ k, BitVec k) = ⟨p.len, val ξ p⟩ := by
  unfold val
  generalize graph.evalRec ξ p.fin = x
  exact sigma_mk_cast_eq (graph_len_fin p) x

theorem graph_point_fin (ξ : Rec) (h : Name) :
    graph.point (graph.evalRec ξ) h.fin = (hashParent h).map fun p => pointOf ξ h p := by
  unfold Graph.point
  rw [graph_kind_fin]
  cases h <;> simp only [kindOf, hashParent, Option.map_some, Option.map_none, pointOf]
  case ch k t => exact congrArg some (Prod.ext rfl (sigma_val ξ (prev k t)))
  case rh => exact congrArg some (Prod.ext rfl (sigma_val ξ rc))

/-- The cache written by key generation. -/
def kc (ξ : Rec) : Cache paperParams := graph.keygenCache ξ

theorem kc_apply_iff (ξ : Rec) (q : Query) (w : BitVec 256) :
    kc ξ q = some w ↔ ∃ h p, hashParent h = some p ∧ q = pointOf ξ h p ∧ w = ξ.2 h.fin := by
  refine (Graph.keygenCache_apply_iff graph ξ q w).trans ?_
  constructor
  · rintro ⟨v, hv, rfl⟩
    obtain ⟨h, rfl⟩ : ∃ h : Name, h.fin = v := ⟨ofFin v, fin_ofFin v⟩
    rw [graph_point_fin, Option.map_eq_some_iff] at hv
    obtain ⟨p, hp, rfl⟩ := hv
    exact ⟨h, p, hp, rfl, rfl⟩
  · rintro ⟨h, p, hp, rfl, rfl⟩
    exact ⟨h.fin, by rw [graph_point_fin, hp]; rfl, rfl⟩

theorem kc_isSome_iff (ξ : Rec) (q : Query) :
    (kc ξ q).isSome ↔ ∃ h p, hashParent h = some p ∧ q = pointOf ξ h p := by
  rw [Option.isSome_iff_exists]
  constructor
  · rintro ⟨w, hw⟩
    obtain ⟨h, p, hp, hq, -⟩ := (kc_apply_iff ξ q w).1 hw
    exact ⟨h, p, hp, hq⟩
  · rintro ⟨h, p, hp, hq⟩
    exact ⟨_, (kc_apply_iff ξ q _).2 ⟨h, p, hp, hq, rfl⟩⟩

theorem kc_enc (ξ : Rec) (k : ℕ) (u : BitVec k) : kc ξ (.enc, ⟨k, u⟩) = none := by
  rcases hk : kc ξ (.enc, ⟨k, u⟩) with _ | w
  · rfl
  · obtain ⟨h, p, -, hq, -⟩ := (kc_apply_iff ξ _ w).1 hk
    exact absurd (congrArg Prod.fst hq) (by simp [pointOf])

/-! ## Exposed and hidden points -/

/-- After signing at the disclosure set `A`, the points of the hash nodes evaluated at `A` are
exposed; when signing failed (`none`), nothing is exposed. -/
def Exposed (A? : Option (Finset Name)) (h : Name) : Prop := ∃ A, A? = some A ∧ Evaluated A h

theorem exposed_some_iff_evaluated (A : Finset Name) (h : Name) : Exposed (some A) h ↔ Evaluated A h := by
  simp [Exposed]

theorem not_exposed_none (h : Name) : ¬ Exposed none h := by
  rintro ⟨A, hA, -⟩
  cases hA

/-- The exposed part of the keygen cache. -/
def fExp (A? : Option (Finset Name)) (ξ : Rec) : Cache paperParams := fun q =>
  if ∃ h p, hashParent h = some p ∧ Exposed A? h ∧ q = pointOf ξ h p then kc ξ q else none

/-- The hidden part of the keygen cache. -/
def fHid (A? : Option (Finset Name)) (ξ : Rec) : Cache paperParams := fun q =>
  if ∃ h p, hashParent h = some p ∧ ¬ Exposed A? h ∧ q = pointOf ξ h p then kc ξ q else none

theorem extend_fExp_fHid (A? : Option (Finset Name)) (ξ : Rec) :
    Cache.extend (fExp A? ξ) (fHid A? ξ) = kc ξ := by
  funext q
  simp only [Cache.extend_apply, fExp, fHid]
  by_cases h1 : ∃ h p, hashParent h = some p ∧ Exposed A? h ∧ q = pointOf ξ h p
  · rw [if_pos h1]
    obtain ⟨h, p, hp, -, hq⟩ := h1
    obtain ⟨w, hw⟩ := Option.isSome_iff_exists.1 ((kc_isSome_iff ξ q).2 ⟨h, p, hp, hq⟩)
    rw [hw]
    rfl
  · rw [if_neg h1, Option.none_or]
    by_cases h2 : ∃ h p, hashParent h = some p ∧ ¬ Exposed A? h ∧ q = pointOf ξ h p
    · rw [if_pos h2]
    · rw [if_neg h2]
      rcases hk : kc ξ q with _ | w
      · rfl
      · exfalso
        obtain ⟨h, p, hp, hq, -⟩ := (kc_apply_iff ξ q w).1 hk
        by_cases he : Exposed A? h
        · exact h1 ⟨h, p, hp, he, hq⟩
        · exact h2 ⟨h, p, hp, he, hq⟩

theorem disjoint_fExp_fHid (A? : Option (Finset Name)) (ξ : Rec) :
    Cache.Disjoint (fExp A? ξ) (fHid A? ξ) := by
  intro q hq
  simp only [fHid] at hq
  split_ifs at hq with h2
  · obtain ⟨h, p, hp, he, hq⟩ := h2
    simp only [fExp]
    rw [if_neg]
    rintro ⟨h', p', hp', he', hq'⟩
    rw [hq] at hq'
    obtain rfl := pointOf_inj_left hq'
    exact he he'
  · simp at hq

theorem fExp_isSome_iff (A? : Option (Finset Name)) (ξ : Rec) (q : Query) :
    (fExp A? ξ q).isSome ↔ ∃ h p, hashParent h = some p ∧ Exposed A? h ∧ q = pointOf ξ h p := by
  simp only [fExp]
  split_ifs with hc
  · obtain ⟨h, p, hp, -, hq⟩ := id hc
    exact iff_of_true ((kc_isSome_iff ξ q).2 ⟨h, p, hp, hq⟩) hc
  · exact iff_of_false (by simp) hc

theorem fHid_isSome_iff (A? : Option (Finset Name)) (ξ : Rec) (q : Query) :
    (fHid A? ξ q).isSome ↔ ∃ h p, hashParent h = some p ∧ ¬ Exposed A? h ∧ q = pointOf ξ h p := by
  simp only [fHid]
  split_ifs with hc
  · obtain ⟨h, p, hp, -, hq⟩ := id hc
    exact iff_of_true ((kc_isSome_iff ξ q).2 ⟨h, p, hp, hq⟩) hc
  · exact iff_of_false (by simp) hc

theorem fHid_none (ξ : Rec) : fHid none ξ = kc ξ := by
  funext q
  simp only [fHid]
  split_ifs with hc
  · rfl
  · rcases hk : kc ξ q with _ | w
    · rfl
    · exfalso
      obtain ⟨h, p, hp, hq, -⟩ := (kc_apply_iff ξ q w).1 hk
      exact hc ⟨h, p, hp, not_exposed_none h, hq⟩

theorem fExp_none (ξ : Rec) : fExp none ξ = ∅ := by
  funext q
  simp only [fExp]
  rw [if_neg]
  · rfl
  · rintro ⟨h, -, -, he, -⟩
    exact not_exposed_none h he

theorem fExp_enc (A? : Option (Finset Name)) (ξ : Rec) (k : ℕ) (u : BitVec k) :
    fExp A? ξ (.enc, ⟨k, u⟩) = none := by
  simp only [fExp]
  rw [if_neg]
  rintro ⟨h, p, -, -, hq⟩
  exact absurd (congrArg Prod.fst hq) (by simp [pointOf])

theorem fHid_enc (A? : Option (Finset Name)) (ξ : Rec) (k : ℕ) (u : BitVec k) :
    fHid A? ξ (.enc, ⟨k, u⟩) = none := by
  simp only [fHid]
  rw [if_neg]
  rintro ⟨h, p, -, -, hq⟩
  exact absurd (congrArg Prod.fst hq) (by simp [pointOf])

/-- A hidden point, when the cache came from a cut, is the point of a hash node that is not
evaluated. -/
theorem fHid_isSome_some_iff (A : Finset Name) (ξ : Rec) (q : Query) :
    (fHid (some A) ξ q).isSome ↔ ∃ h p, hashParent h = some p ∧ ¬ Evaluated A h ∧ q = pointOf ξ h p := by
  simp only [fHid_isSome_iff, exposed_some_iff_evaluated]

/-! ## The event `Spr` -/

/-- Some cached answer, at a point with the label of a hash node but an input different from the
honest one, begins with the honest output of that node. -/
def Spr (c : Cache paperParams) (ξ : Rec) : Prop :=
  ∃ h p, hashParent h = some p ∧ ∃ u : BitVec p.len, u ≠ val ξ p ∧
    ∃ w, c (.node h.idx, ⟨p.len, u⟩) = some w ∧ trunc w = trunc (ξ.2 h.fin)

theorem Spr.mono {c c' : Cache paperParams} (h : Cache.Sub c c') {ξ : Rec} (hs : Spr c ξ) :
    Spr c' ξ := by
  obtain ⟨hn, p, hp, u, hu, w, hw, ht⟩ := hs
  exact ⟨hn, p, hp, u, hu, w, h _ _ hw, ht⟩

theorem spr_cacheQuery_enc (c : Cache paperParams) (ξ : Rec) (k : ℕ) (u : BitVec k)
    (w : BitVec 256) : Spr (c.cacheQuery (.enc, ⟨k, u⟩) w) ξ ↔ Spr c ξ := by
  have key : ∀ (h p : Name) (u' : BitVec p.len),
      c.cacheQuery (.enc, ⟨k, u⟩) w (.node h.idx, ⟨p.len, u'⟩) = c (.node h.idx, ⟨p.len, u'⟩) :=
    fun h p u' => QueryCache.cacheQuery_of_ne _ _ (by simp)
  simp only [Spr, key]

/-- An entry of an overlay is an entry of one of the two caches. -/
theorem spr_of_extend {c f : Cache paperParams} {ξ : Rec} (hs : Spr (Cache.extend c f) ξ) :
    Spr c ξ ∨ Spr f ξ := by
  obtain ⟨h, p, hp, u, hu, w, hw, ht⟩ := hs
  rw [Cache.extend_apply, Option.or_eq_some_iff] at hw
  rcases hw with hw | ⟨-, hw⟩
  · exact Or.inl ⟨h, p, hp, u, hu, w, hw, ht⟩
  · exact Or.inr ⟨h, p, hp, u, hu, w, hw, ht⟩

theorem spr_extend (c f : Cache paperParams) (ξ : Rec) (hd : Cache.Disjoint c f) :
    Spr (Cache.extend c f) ξ ↔ Spr c ξ ∨ Spr f ξ := by
  constructor
  · exact spr_of_extend
  · rintro (⟨h, p, hp, u, hu, w, hw, ht⟩ | ⟨h, p, hp, u, hu, w, hw, ht⟩)
    · exact ⟨h, p, hp, u, hu, w, Cache.extend_apply_of_some hw, ht⟩
    · refine ⟨h, p, hp, u, hu, w, ?_, ht⟩
      rw [Cache.extend_apply_of_none (hd _ (by rw [hw]; rfl))]
      exact hw

theorem not_spr_kc (ξ : Rec) : ¬ Spr (kc ξ) ξ := by
  rintro ⟨h, p, hp, u, hu, w, hw, -⟩
  obtain ⟨h', p', hp', hq, -⟩ := (kc_apply_iff ξ _ w).1 hw
  have hh : h = h' := Name.idx_injective (by simpa [pointOf] using congrArg Prod.fst hq)
  subst hh
  rw [hp] at hp'
  obtain rfl := Option.some.inj hp'
  exact hu (eq_of_heq (Sigma.mk.inj_iff.1 (congrArg Prod.snd hq)).2)

theorem sub_fExp_kc (A? : Option (Finset Name)) (ξ : Rec) : Cache.Sub (fExp A? ξ) (kc ξ) := by
  intro q w hw
  simp only [fExp] at hw
  by_cases hc : ∃ h p, hashParent h = some p ∧ Exposed A? h ∧ q = pointOf ξ h p
  · rwa [if_pos hc] at hw
  · rw [if_neg hc] at hw
    cases hw

theorem not_spr_fExp (A? : Option (Finset Name)) (ξ : Rec) : ¬ Spr (fExp A? ξ) ξ :=
  fun hs => not_spr_kc ξ (hs.mono (sub_fExp_kc A? ξ))

theorem not_spr_empty (ξ : Rec) : ¬ Spr ∅ ξ := by
  rintro ⟨h, p, hp, u, hu, w, hw, -⟩
  simp at hw

/-- `ε = 2 ^ (-128)`. -/
def ε : ℝ≥0∞ := ((2 : ℝ≥0∞) ^ 128)⁻¹

/-- At most `2 ^ 128` values of `256` bits have a given truncation. -/
theorem card_filter_trunc_le (a : BitVec 128) :
    (Finset.univ.filter fun w : BitVec 256 => trunc w = a).card ≤ 2 ^ 128 := by
  have key : (Finset.univ.filter fun w : BitVec 256 => trunc w = a).card ≤
      (Finset.univ : Finset (BitVec 128)).card := by
    refine Finset.card_le_card_of_injOn (fun w => (w >>> 128).setWidth 128)
      (fun _ _ => Finset.mem_univ _) ?_
    intro w hw w' hw' e
    rw [Finset.mem_coe, Finset.mem_filter] at hw hw'
    have hlow : ∀ i, i < 128 → w.getLsbD i = w'.getLsbD i := by
      intro i hi
      have := congrArg (fun x : BitVec 128 => x.getLsbD i) (hw.2.trans hw'.2.symm)
      simpa [trunc, BitVec.getLsbD_setWidth, hi] using this
    have hhigh : ∀ i, 128 ≤ i → i < 256 → w.getLsbD i = w'.getLsbD i := by
      intro i hi1 hi2
      have := congrArg (fun x : BitVec 128 => x.getLsbD (i - 128)) e
      have h1 : i - 128 < 128 := by omega
      have h2 : 128 + (i - 128) = i := by omega
      simpa [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, h1, h2] using this
    apply BitVec.eq_of_getLsbD_eq
    intro i hi2
    by_cases hi : i < 128
    · exact hlow i hi
    · exact hhigh i (by omega) hi2
  rw [Finset.card_univ, Fintype.card_bitVec] at key
  exact key

theorem inv_card_bitVec_mul_two_pow : (Fintype.card (BitVec 256) : ℝ≥0∞)⁻¹ * ((2 ^ 128 : ℕ) : ℝ≥0∞) = ε := by
  have h0 : (2 : ℝ≥0∞) ^ 128 ≠ 0 := pow_ne_zero _ two_ne_zero
  have ht : (2 : ℝ≥0∞) ^ 128 ≠ ⊤ := ENNReal.pow_ne_top ENNReal.ofNat_ne_top
  have e : (2 : ℝ≥0∞) ^ 128 * 2 ^ 128 = 2 ^ 256 := by rw [← pow_add]
  rw [Fintype.card_bitVec, ε]
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  rw [← e, ENNReal.mul_inv (Or.inl h0) (Or.inl ht), mul_assoc, ENNReal.inv_mul_cancel h0 ht,
    mul_one]

/-- A fresh answer creates a `Spr` entry with probability at most `ε`. -/
theorem spr_charge (c : Cache paperParams) (ξ : Rec) (q : Query) (hq : c q = none) :
    ∑ w : BitVec 256, (Fintype.card (BitVec 256) : ℝ≥0∞)⁻¹ *
        (if Spr (c.cacheQuery q w) ξ then 1 else 0) ≤ (if Spr c ξ then 1 else 0) + ε := by
  by_cases hs : Spr c ξ
  · rw [if_pos hs]
    calc ∑ w : BitVec 256, (Fintype.card (BitVec 256) : ℝ≥0∞)⁻¹ *
          (if Spr (c.cacheQuery q w) ξ then 1 else 0)
        ≤ ∑ w : BitVec 256, (Fintype.card (BitVec 256) : ℝ≥0∞)⁻¹ * 1 := by
          refine Finset.sum_le_sum fun w _ => mul_le_mul_of_nonneg_left ?_ zero_le
          split_ifs <;> simp
      _ = 1 := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
            ENNReal.mul_inv_cancel (by exact_mod_cast Fintype.card_ne_zero)
              (ENNReal.natCast_ne_top _)]
      _ ≤ 1 + ε := le_self_add
  · rw [if_neg hs, zero_add]
    have key : ∀ w, Spr (c.cacheQuery q w) ξ →
        ∃ h p, hashParent h = some p ∧ ∃ u : BitVec p.len, u ≠ val ξ p ∧
          q = (.node h.idx, ⟨p.len, u⟩) ∧ trunc w = trunc (ξ.2 h.fin) := by
      rintro w ⟨h, p, hp, u, hu, w', hw', ht⟩
      by_cases hqq : ((Label.node h.idx, ⟨p.len, u⟩) : Query) = q
      · subst hqq
        rw [QueryCache.cacheQuery_self] at hw'
        obtain rfl := Option.some.inj hw'
        exact ⟨h, p, hp, u, hu, rfl, ht⟩
      · rw [QueryCache.cacheQuery_of_ne _ _ hqq] at hw'
        exact (hs ⟨h, p, hp, u, hu, w', hw', ht⟩).elim
    by_cases hex : ∃ h p, hashParent h = some p ∧
        ∃ u : BitVec p.len, q = (.node h.idx, ⟨p.len, u⟩)
    · obtain ⟨h₀, p₀, hp₀, u₀, rfl⟩ := hex
      have key' : ∀ w, Spr (c.cacheQuery (.node h₀.idx, ⟨p₀.len, u₀⟩) w) ξ →
          trunc w = trunc (ξ.2 h₀.fin) := by
        intro w hw
        obtain ⟨h, p, -, u, -, hq', ht⟩ := key w hw
        have : h₀ = h := Name.idx_injective (by simpa using congrArg Prod.fst hq')
        subst this
        exact ht
      calc ∑ w : BitVec 256, (Fintype.card (BitVec 256) : ℝ≥0∞)⁻¹ *
            (if Spr (c.cacheQuery (.node h₀.idx, ⟨p₀.len, u₀⟩) w) ξ then 1 else 0)
          ≤ ∑ w : BitVec 256, (Fintype.card (BitVec 256) : ℝ≥0∞)⁻¹ *
            (if trunc w = trunc (ξ.2 h₀.fin) then 1 else 0) := by
            refine Finset.sum_le_sum fun w _ => mul_le_mul_of_nonneg_left ?_ zero_le
            split_ifs with h1 h2
            · exact le_rfl
            · exact absurd (key' w h1) h2
            · exact zero_le_one
            · exact le_rfl
        _ = (Fintype.card (BitVec 256) : ℝ≥0∞)⁻¹ *
            ((Finset.univ.filter fun w : BitVec 256 => trunc w = trunc (ξ.2 h₀.fin)).card :
              ℝ≥0∞) := by
            rw [← Finset.mul_sum, Finset.sum_boole]
        _ ≤ (Fintype.card (BitVec 256) : ℝ≥0∞)⁻¹ * ((2 ^ 128 : ℕ) : ℝ≥0∞) :=
            mul_le_mul_of_nonneg_left (Nat.cast_le.2 (card_filter_trunc_le _)) zero_le
        _ = ε := inv_card_bitVec_mul_two_pow
    · have hno : ∀ w, ¬ Spr (c.cacheQuery q w) ξ := fun w hw => by
        obtain ⟨h, p, hp, u, -, hq', -⟩ := key w hw
        exact hex ⟨h, p, hp, u, hq'⟩
      rw [Finset.sum_eq_zero fun w _ => by rw [if_neg (hno w), mul_zero]]
      exact zero_le

/-! ## Coordinates -/

/-- The record coordinates that the value of a node reads. -/
def deps : Name → Finset Name
  | src k => {src k}
  | ch k t => {ch k t}
  | cv k t => {ch k t}
  | rc => Finset.univ.image fun k => ch k 19
  | rh => {rh}

theorem child_cv_19 (k : Fin 41) : child (cv k 19) = some rc := rfl

/-- Every coordinate a node reads is the node itself or lies at most two steps below it. -/
theorem mem_deps_cases {s n : Name} (h : s ∈ deps n) :
    s = n ∨ child s = some n ∨ ∃ m, child s = some m ∧ child m = some n := by
  cases n with
  | src k => exact Or.inl (Finset.mem_singleton.1 h)
  | ch k t => exact Or.inl (Finset.mem_singleton.1 h)
  | cv k t =>
    obtain rfl := Finset.mem_singleton.1 h
    exact Or.inr (Or.inl rfl)
  | rc =>
    simp only [deps, Finset.mem_image, Finset.mem_univ, true_and] at h
    obtain ⟨k, rfl⟩ := h
    exact Or.inr (Or.inr ⟨cv k 19, rfl, child_cv_19 k⟩)
  | rh => exact Or.inl (Finset.mem_singleton.1 h)

/-- Resample a source. -/
def updSrc (ξ : Rec) (k : Fin 41) (b : BitVec 128) : Rec :=
  (Function.update ξ.1 (src k).fin (b.cast (graph_len_fin (src k)).symm), ξ.2)

/-- Resample a hash output. -/
def updHash (ξ : Rec) (s : Name) (b : BitVec 256) : Rec := (ξ.1, Function.update ξ.2 s.fin b)

theorem updHash_snd_self (ξ : Rec) (s : Name) (b : BitVec 256) : (updHash ξ s b).2 s.fin = b :=
  Function.update_self _ _ _

theorem updHash_snd_ne (ξ : Rec) (s : Name) (b : BitVec 256) {n : Name} (h : n ≠ s) :
    (updHash ξ s b).2 n.fin = ξ.2 n.fin := by
  simp only [updHash]
  exact Function.update_of_ne (fun e => h (Name.fin_injective e)) _ _

theorem updSrc_snd (ξ : Rec) (k : Fin 41) (b : BitVec 128) : (updSrc ξ k b).2 = ξ.2 := rfl

theorem val_updHash_of_not_mem_deps (ξ : Rec) (s : Name) (b : BitVec 256) (n : Name)
    (h : s ∉ deps n) : val (updHash ξ s b) n = val ξ n := by
  cases n with
  | src k =>
    rw [val_src, val_src]
    rfl
  | ch k t =>
    simp only [deps, Finset.mem_singleton] at h
    rw [val_ch, val_ch, updHash_snd_ne _ _ _ (Ne.symm h)]
  | cv k t =>
    simp only [deps, Finset.mem_singleton] at h
    rw [val_cv, val_cv, updHash_snd_ne _ _ _ (Ne.symm h)]
  | rc =>
    simp only [deps, Finset.mem_image, Finset.mem_univ, true_and, not_exists] at h
    rw [val_rc, val_rc]
    exact congrArg cat41 (funext fun k => by rw [updHash_snd_ne _ _ _ (h k)])
  | rh =>
    simp only [deps, Finset.mem_singleton] at h
    rw [val_rh, val_rh, updHash_snd_ne _ _ _ (Ne.symm h)]

theorem val_updSrc_of_not_mem_deps (ξ : Rec) (k : Fin 41) (b : BitVec 128) (n : Name)
    (h : src k ∉ deps n) : val (updSrc ξ k b) n = val ξ n := by
  cases n with
  | src k' =>
    simp only [deps, Finset.mem_singleton, Name.src.injEq] at h
    have e : (updSrc ξ k b).1 (src k').fin = ξ.1 (src k').fin :=
      Function.update_of_ne (fun e => h (Name.src.inj (Name.fin_injective e)).symm) _ _
    rw [val_src, val_src, e]
  | ch k t => rw [val_ch, val_ch, updSrc_snd]
  | cv k t => rw [val_cv, val_cv, updSrc_snd]
  | rc => rw [val_rc, val_rc, updSrc_snd]
  | rh => rw [val_rh, val_rh, updSrc_snd]

theorem val_updSrc_self (ξ : Rec) (k : Fin 41) (b : BitVec 128) :
    val (updSrc ξ k b) (src k) = b := by
  have e : (updSrc ξ k b).1 (src k).fin = b.cast (graph_len_fin (src k)).symm :=
    Function.update_self _ _ _
  rw [val_src, e]
  exact cast_cast_eq _ _ _

theorem snd_updHash_of_ne (ξ : Rec) (s : Name) (b : BitVec 256) (n : Name) (h : n ≠ s) :
    (updHash ξ s b).2 n.fin = ξ.2 n.fin :=
  updHash_snd_ne ξ s b h

theorem snd_updHash_self (ξ : Rec) (s : Name) (b : BitVec 256) :
    (updHash ξ s b).2 s.fin = b :=
  updHash_snd_self ξ s b

theorem snd_updSrc (ξ : Rec) (k : Fin 41) (b : BitVec 128) : (updSrc ξ k b).2 = ξ.2 := rfl

/-! ## The coordinate that randomizes the input of a hash node -/

/-- The coordinate resampled to randomize the input of a hash node (junk for other nodes). -/
def coordOf : Name → Name
  | ch k t => if h : t.val = 0 then src k else ch k ⟨t.val - 1, by omega⟩
  | rh => ch 40 19
  | n => n

theorem coordOf_ne_rh (h : Name) (hh : h.cost ≠ 0) : coordOf h ≠ rh := by
  cases h
  case ch k t =>
    simp only [coordOf]
    split_ifs <;> simp
  case rh => simp [coordOf]
  all_goals exact absurd rfl hh

/-- The coordinate of a hash node lies at most two steps below its parent. -/
theorem coordOf_below {h p : Name} (hp : hashParent h = some p) :
    coordOf h = p ∨ child (coordOf h) = some p ∨ ∃ m, child (coordOf h) = some m ∧ child m = some p := by
  cases h <;> simp only [hashParent, Option.some.injEq, reduceCtorEq] at hp <;> subst hp
  · simp only [coordOf, Name.prev]
    split_ifs with ht
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr ⟨cv 40 19, rfl, rfl⟩)

theorem trunc_append_right {n : ℕ} (x : BitVec n) (y : BitVec 128) : trunc (x ++ y) = y := by
  unfold trunc
  rw [BitVec.setWidth_append, dif_pos le_rfl, BitVec.setWidth_eq]

theorem trunc_catN_succ (n : ℕ) (a : Fin (n + 1) → BitVec 128) :
    trunc (catN (n + 1) a) = a (Fin.last n) := by
  show trunc (((catN n fun i => a i.castSucc) ++ a (Fin.last n)).cast _) = _
  rw [trunc_cast, trunc_append_right]

theorem trunc_cat41 (a : Fin 41 → BitVec 128) : trunc (cat41 a) = a 40 := by
  unfold cat41
  rw [trunc_cast]
  exact trunc_catN_succ 40 a

theorem trunc_of_cat41_eq {a : Fin 41 → BitVec 128} {u : BitVec 5248} (e : cat41 a = u) :
    trunc u = a 40 := by
  subst e
  exact trunc_cat41 a

/-- A filter whose members all have the same truncation has at most `2 ^ 128` elements. -/
theorem card_filter_le_of_imp (p : BitVec 256 → Prop) [DecidablePred p] (a : BitVec 128)
    (hp : ∀ b, p b → trunc b = a) : (Finset.univ.filter p).card ≤ 2 ^ 128 :=
  le_trans (Finset.card_le_card fun b hb => Finset.mem_filter.2
    ⟨Finset.mem_univ _, hp b (Finset.mem_filter.1 hb).2⟩) (card_filter_trunc_le a)

/-- Resampling the coordinate of a hash node makes its input hit any given value with
probability at most `2 ^ (-128)`: hash coordinates. -/
theorem card_updHash_input_le {h p : Name} (hp : hashParent h = some p) (ξ : Rec)
    (hs : ∀ k, coordOf h ≠ src k) (u : BitVec p.len) :
    (Finset.univ.filter fun b : BitVec 256 => val (updHash ξ (coordOf h) b) p = u).card ≤ 2 ^ 128 := by
  cases h <;> simp only [hashParent, Option.some.injEq, reduceCtorEq] at hp <;> subst hp
  · -- `ch k t`
    rename_i k t
    have ht : ¬ t.val = 0 := fun ht => hs k (by simp [coordOf, ht])
    have e1 : coordOf (ch k t) = ch k ⟨t.val - 1, by omega⟩ := by simp [coordOf, ht]
    have e2 : prev k t = cv k ⟨t.val - 1, by omega⟩ := by simp [Name.prev, ht]
    revert u
    rw [e1, e2]
    intro u
    refine card_filter_le_of_imp _ u fun b hb => ?_
    rw [val_cv, updHash_snd_self] at hb
    exact hb
  · -- `rh`
    refine card_filter_le_of_imp _ (trunc u) fun b hb => ?_
    rw [val_rc] at hb
    have := trunc_of_cat41_eq hb
    exact (this.trans (congrArg trunc (updHash_snd_self _ _ _))).symm

/-- Source coordinates. -/
theorem card_updSrc_input_le {h p : Name} (hp : hashParent h = some p) (ξ : Rec) {k : Fin 41}
    (hs : coordOf h = src k) (u : BitVec p.len) :
    (Finset.univ.filter fun b : BitVec 128 => val (updSrc ξ k b) p = u).card ≤ 1 := by
  cases h <;> simp only [hashParent, Option.some.injEq, reduceCtorEq] at hp <;> subst hp <;>
    simp only [coordOf] at hs
  · rename_i k' t
    by_cases ht : t.val = 0
    · rw [dif_pos ht] at hs
      obtain rfl : k = k' := (Name.src.inj hs).symm
      have e : prev k t = src k := by simp [Name.prev, ht]
      revert u
      rw [e]
      intro u
      rw [Finset.card_le_one]
      intro a ha b hb
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, val_updSrc_self] at ha hb
      exact ha.trans hb.symm
    · rw [dif_neg ht] at hs
      exact absurd hs (by simp)
  · exact absurd hs (by simp)

end Flat

end OptimalOTS
