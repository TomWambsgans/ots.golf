import OptimalOTS.Statement

/-!
# Caches of the lazy random oracle

Generic facts about `oracleImpl P` (the lazy random oracle of `OptimalOTS.Statement`) used by the
bare-oracle lower-bound analysis:

* `extend c f` overlays the cache `f` under the cache `c` (entries of `c` take priority);
* `Hits c f` says that some point cached in `f` is also cached in `c`;
* the one-step run lemmas of `oracleImpl P`;
* runs only grow the cache (`sub_of_mem_support_run`).
-/

open OracleSpec OracleComp ENNReal

noncomputable section

open scoped Classical

namespace OptimalOTS

/-- The cache of the random oracle. -/
abbrev Cache (P : Params) := (hashSpec P).QueryCache

/-- The lazy random oracle run from cache `c`. -/
abbrev run (P : Params) {α : Type} (oa : OracleComp (Spec P) α) (c : Cache P) :
    ProbComp (α × Cache P) :=
  (simulateQ (oracleImpl P) oa).run c

namespace Cache

variable {P : Params}

/-- Overlay `f` under `c`: entries of `c` take priority. -/
def extend (c f : Cache P) : Cache P := fun q => (c q).or (f q)

/-- Some point cached in `f` is cached in `c`. -/
def Hits (c f : Cache P) : Prop := ∃ q, (f q).isSome ∧ (c q).isSome

/-- `c` has no point in common with `f`. -/
def Disjoint (c f : Cache P) : Prop := ∀ q, (f q).isSome → c q = none

/-- Every entry of `c` is an entry of `c'`. -/
def Sub (c c' : Cache P) : Prop := ∀ q u, c q = some u → c' q = some u

theorem Sub.refl (c : Cache P) : Sub c c := fun _ _ h => h

theorem Sub.trans {c₁ c₂ c₃ : Cache P} (h₁ : Sub c₁ c₂) (h₂ : Sub c₂ c₃) : Sub c₁ c₃ :=
  fun q u h => h₂ q u (h₁ q u h)

theorem Sub.isSome {c c' : Cache P} (h : Sub c c') {q : Query} (hq : (c q).isSome) :
    (c' q).isSome := by
  obtain ⟨u, hu⟩ := Option.isSome_iff_exists.1 hq
  rw [h q u hu]; rfl

@[simp] theorem extend_apply (c f : Cache P) (q : Query) : extend c f q = (c q).or (f q) := rfl

theorem extend_apply_of_some {c f : Cache P} {q : Query} {u : BitVec P.hashBits}
    (h : c q = some u) : extend c f q = some u := by simp [extend, h]

theorem extend_apply_of_none {c f : Cache P} {q : Query} (h : c q = none) :
    extend c f q = f q := by simp [extend, h]

@[simp] theorem extend_empty (c : Cache P) : extend c ∅ = c := by
  funext q; simp [extend]

@[simp] theorem empty_extend (f : Cache P) : extend ∅ f = f := by
  funext q; simp [extend]

theorem extend_cacheQuery (c f : Cache P) (q : Query) (u : BitVec P.hashBits) :
    extend (c.cacheQuery q u) f = (extend c f).cacheQuery q u := by
  funext q'
  by_cases h : q' = q
  · subst h; simp [extend]
  · simp [extend, QueryCache.cacheQuery_of_ne _ _ h]

theorem extend_assoc (c f g : Cache P) : extend (extend c f) g = extend c (extend f g) := by
  funext q; simp [extend, Option.or_assoc]

theorem extend_isSome (c f : Cache P) (q : Query) :
    (extend c f q).isSome ↔ (c q).isSome ∨ (f q).isSome := by
  simp [extend, Option.isSome_or]

theorem not_hits_empty (f : Cache P) : ¬ Hits ∅ f := by
  rintro ⟨q, -, h⟩; simp at h

theorem Disjoint.not_hits {c f : Cache P} (h : Disjoint c f) : ¬ Hits c f := by
  rintro ⟨q, hf, hc⟩
  rw [h q hf] at hc; simp at hc

theorem not_hits_iff_disjoint (c f : Cache P) : ¬ Hits c f ↔ Disjoint c f := by
  constructor
  · intro h q hf
    by_contra hc
    exact h ⟨q, hf, Option.ne_none_iff_isSome.1 hc⟩
  · exact Disjoint.not_hits

theorem hits_cacheQuery (c f : Cache P) (q : Query) (u : BitVec P.hashBits) :
    Hits (c.cacheQuery q u) f ↔ Hits c f ∨ (f q).isSome := by
  constructor
  · rintro ⟨q', hf, hc⟩
    by_cases h : q' = q
    · subst h; exact Or.inr hf
    · rw [QueryCache.cacheQuery_of_ne _ _ h] at hc
      exact Or.inl ⟨q', hf, hc⟩
  · rintro (⟨q', hf, hc⟩ | hf)
    · by_cases h : q' = q
      · subst h; exact ⟨q', hf, by simp⟩
      · exact ⟨q', hf, by rw [QueryCache.cacheQuery_of_ne _ _ h]; exact hc⟩
    · exact ⟨q, hf, by simp⟩

theorem hits_extend (c f g : Cache P) : Hits (extend c f) g ↔ Hits c g ∨ Hits f g := by
  constructor
  · rintro ⟨q, hg, hc⟩
    rw [extend_isSome] at hc
    rcases hc with hc | hc
    · exact Or.inl ⟨q, hg, hc⟩
    · exact Or.inr ⟨q, hg, hc⟩
  · rintro (⟨q, hg, hc⟩ | ⟨q, hg, hc⟩)
    · exact ⟨q, hg, (extend_isSome c f q).2 (Or.inl hc)⟩
    · exact ⟨q, hg, (extend_isSome c f q).2 (Or.inr hc)⟩

theorem Hits.mono_left {c c' f : Cache P} (h : Hits c f) (hle : Sub c c') : Hits c' f := by
  obtain ⟨q, hf, hc⟩ := h
  exact ⟨q, hf, hle.isSome hc⟩

theorem Hits.mono_right {c f f' : Cache P} (h : Hits c f) (hle : Sub f f') : Hits c f' := by
  obtain ⟨q, hf, hc⟩ := h
  exact ⟨q, hle.isSome hf, hc⟩

theorem disjoint_cacheQuery {c f : Cache P} (h : Disjoint c f) {q : Query}
    (hq : f q = none) (u : BitVec P.hashBits) : Disjoint (c.cacheQuery q u) f := by
  intro q' hq'
  have hne : q' ≠ q := fun e => by rw [e, hq] at hq'; simp at hq'
  rw [QueryCache.cacheQuery_of_ne _ _ hne]
  exact h q' hq'

theorem sub_cacheQuery_of_none {c : Cache P} {q : Query} (h : c q = none)
    (u : BitVec P.hashBits) : Sub c (c.cacheQuery q u) := by
  intro q' u' hq'
  have hne : q' ≠ q := fun e => by rw [e, h] at hq'; cases hq'
  rw [QueryCache.cacheQuery_of_ne _ _ hne]; exact hq'

end Cache

/-! ## One-step run lemmas for the lazy oracle -/

theorem oracleImpl_run_inl (P : Params) (c : Cache P) (t : ℕ) :
    (oracleImpl P (.inl t)).run c =
      HasQuery.query (spec := unifSpec) (m := ProbComp) t >>= fun u => pure (u, c) := by
  simp [oracleImpl, StateT.run_monadLift]

theorem oracleImpl_run_inr_none (P : Params) {c : Cache P} {q : Query} (hc : c q = none) :
    (oracleImpl P (.inr q)).run c =
      ($ᵗ BitVec P.hashBits) >>= fun u => pure (u, c.cacheQuery q u) := by
  have := randomOracle.run_eq (spec₀ := hashSpec P) q c
  rw [hc] at this
  exact this

theorem oracleImpl_run_inr_some (P : Params) {c : Cache P} {q : Query} {u : BitVec P.hashBits}
    (hc : c q = some u) : (oracleImpl P (.inr q)).run c = pure (u, c) := by
  have := randomOracle.run_eq (spec₀ := hashSpec P) q c
  rw [hc] at this
  exact this

theorem run_pure (P : Params) {α : Type} (x : α) (c : Cache P) :
    run P (pure x) c = pure (x, c) := by
  simp [run]

theorem run_query_bind (P : Params) {α : Type} (t : (Spec P).Domain)
    (k : (Spec P).Range t → OracleComp (Spec P) α) (c : Cache P) :
    run P (liftM ((Spec P).query t) >>= k) c =
      (oracleImpl P t).run c >>= fun p => run P (k p.1) p.2 := by
  simp only [run, simulateQ_bind, simulateQ_spec_query, StateT.run_bind]

theorem run_bind (P : Params) {α β : Type} (oa : OracleComp (Spec P) α)
    (k : α → OracleComp (Spec P) β) (c : Cache P) :
    run P (oa >>= k) c = run P oa c >>= fun p => run P (k p.1) p.2 := by
  simp only [run, simulateQ_bind, StateT.run_bind]

theorem run_map (P : Params) {α β : Type} (oa : OracleComp (Spec P) α) (f : α → β)
    (c : Cache P) :
    run P (f <$> oa) c = (fun p => (f p.1, p.2)) <$> run P oa c := by
  simp only [run, simulateQ_map, StateT.run_map]

theorem run'_eq (P : Params) {α : Type} (oa : OracleComp (Spec P) α) (c : Cache P) :
    (simulateQ (oracleImpl P) oa).run' c = Prod.fst <$> run P oa c := by
  simp [run, StateT.run'_eq]

/-- A lifted `ProbComp` runs unchanged and leaves the cache alone. -/
theorem run_liftM (P : Params) {α : Type} (pc : ProbComp α) (c : Cache P) :
    run P (liftM pc : OracleComp (Spec P) α) c = (fun x => (x, c)) <$> pc := by
  change run P (liftComp pc (Spec P)) c = _
  induction pc using OracleComp.inductionOn generalizing c with
  | pure x => simp [liftComp, run_pure]
  | query_bind t mx ih =>
    rw [liftComp_bind]
    have hq : liftComp (liftM (OracleSpec.query t) : ProbComp _) (Spec P) =
        (liftM ((Spec P).query (.inl t)) : OracleComp (Spec P) _) := by
      simp [liftComp]; rfl
    rw [hq, run_query_bind, oracleImpl_run_inl]
    simp only [bind_assoc, pure_bind, ih, map_bind]
    rfl

/-- Runs only grow the cache. -/
theorem sub_of_mem_support_run (P : Params) {α : Type} (oa : OracleComp (Spec P) α) :
    ∀ (c : Cache P) (p : α × Cache P), p ∈ support (run P oa c) → Cache.Sub c p.2 := by
  induction oa using OracleComp.inductionOn with
  | pure x =>
    intro c p hp
    rw [run_pure, support_pure] at hp
    simp only [Set.mem_singleton_iff] at hp
    subst hp
    exact Cache.Sub.refl c
  | query_bind t k ih =>
    intro c p hp
    rw [run_query_bind, support_bind] at hp
    simp only [Set.mem_iUnion] at hp
    obtain ⟨⟨u, c'⟩, hu, hp⟩ := hp
    rcases t with t | q
    · rw [oracleImpl_run_inl, support_bind] at hu
      simp only [Set.mem_iUnion] at hu
      obtain ⟨w, -, hw⟩ := hu
      simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hw
      obtain ⟨rfl, rfl⟩ := hw
      exact ih u _ p hp
    · rcases hc : c q with _ | v
      · rw [oracleImpl_run_inr_none P hc, support_bind] at hu
        simp only [Set.mem_iUnion] at hu
        obtain ⟨w, -, hw⟩ := hu
        simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hw
        obtain ⟨rfl, rfl⟩ := hw
        exact (Cache.sub_cacheQuery_of_none hc u).trans (ih u _ p hp)
      · rw [oracleImpl_run_inr_some P hc, support_pure] at hu
        simp only [Set.mem_singleton_iff, Prod.mk.injEq] at hu
        obtain ⟨rfl, rfl⟩ := hu
        exact ih u _ p hp

end OptimalOTS
