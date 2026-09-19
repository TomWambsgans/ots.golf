import OptimalOTS.Statement

/-!
# Caches of the lazy random oracle

Generic facts about `oracleImpl P` (the lazy random oracle of `OptimalOTS.Statement`) used by the
bare-oracle lower-bound analysis:

* `Sub c c'`: every entry of `c` is an entry of `c'`;
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

/-- Every entry of `c` is an entry of `c'`. -/
def Sub (c c' : Cache P) : Prop := ∀ q u, c q = some u → c' q = some u

theorem Sub.refl (c : Cache P) : Sub c c := fun _ _ h => h

theorem Sub.trans {c₁ c₂ c₃ : Cache P} (h₁ : Sub c₁ c₂) (h₂ : Sub c₂ c₃) : Sub c₁ c₃ :=
  fun q u h => h₂ q u (h₁ q u h)

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
