import Submissions.Upper.Values
import Submissions.Upper.Reconstruct

/-!
# From an accepted forgery to a bad event

Let the verifier reconstruct the root from values `given` at the disclosure set `A'` and obtain the
assignment `y`, all answers being recorded in the cache `d` (`Graph.ReconEqs`), and accept:
the first 128 bits of `y` at the root are the public key of the honest record `ξ`.

* `up` (the walk in the proof of the paper's Section 7.3): if `y` differs from the honest values at a
  non-hash node visited by the reconstruction, some recorded answer at a non-keygen point begins
  with an honest value (`Spr d ξ`).
* `events_none`: if nothing was exposed, then `Spr d ξ` or the root's keygen point was queried.
* `events_ne`: if the signature revealed the cut `A ≠ A'` of the same cost, then `Spr d ξ` or a
  keygen point hidden at `A` was queried.
* `events_same`: if `A' = A` and the supplied values differ from the honest ones, `Spr d ξ`.
-/

open OracleSpec OracleComp ENNReal

noncomputable section

open scoped Classical

namespace OptimalOTS

namespace Forest

open Name

/-- The verifier's value at a node. -/
def yv (y : graph.Assignment) (n : Name) : BitVec n.len := (y n.fin).cast (graph_len_fin n)

/-! ## Bit-vector helpers -/

theorem sigma_cast {a b : ℕ} (h : a = b) (x : BitVec a) :
    (⟨a, x⟩ : Σ k : ℕ, BitVec k) = ⟨b, x.cast h⟩ := by subst h; rfl

theorem trunc_cast_eq {a b : ℕ} (h : a = b) (x : BitVec a) : trunc (x.cast h) = trunc x := by
  subst h; rfl

theorem trunc_128 (x : BitVec 128) : trunc x = x := BitVec.setWidth_eq x

theorem trunc_eq_cast {m : ℕ} (h : m = 128) (x : BitVec m) : trunc x = x.cast h := by
  subst h; exact BitVec.setWidth_eq x

theorem cast_injective {n m : ℕ} (h : n = m) {x y : BitVec n} (e : x.cast h = y.cast h) :
    x = y := by
  subst h; simpa using e

theorem append_inj {n m : ℕ} {x x' : BitVec n} {y y' : BitVec m} (h : x ++ y = x' ++ y') :
    x = x' ∧ y = y' := by
  have key : ∀ i, (x ++ y).getLsbD i = (x' ++ y').getLsbD i := fun i => by rw [h]
  simp only [BitVec.getLsbD_append] at key
  constructor
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have := key (i + m)
    simp only [show ¬ (i + m < m) by omega, if_false, Nat.add_sub_cancel] at this
    exact this
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have := key i
    simpa [hi] using this

theorem catN_inj : ∀ (n : ℕ) {a b : Fin n → BitVec 128}, catN n a = catN n b → a = b
  | 0, a, b, _ => funext fun i => i.elim0
  | n + 1, a, b, h => by
    have h' : (catN n fun i => a i.castSucc) ++ a (Fin.last n) =
        (catN n fun i => b i.castSucc) ++ b (Fin.last n) := cast_injective _ h
    obtain ⟨h1, h2⟩ := append_inj h'
    have ih := catN_inj n h1
    funext i
    by_cases hi : i.val < n
    · have := congrFun ih ⟨i.val, hi⟩
      simpa using this
    · have e : i = Fin.last n := Fin.ext (by have := i.isLt; simp only [Fin.val_last]; omega)
      rw [e]
      exact h2

theorem cat41_inj {a b : Fin 41 → BitVec 128} (h : cat41 a = cat41 b) : a = b :=
  catN_inj 41 (cast_injective _ h)

/-! ## Names -/

theorem cost_eq_zero_of_len {n : Name} (h : n.len = 128) : n.cost = 0 := by
  cases n <;> first | rfl | (simp [Name.len] at h)

theorem len_eq_of_hashParent {h p : Name} (hp : hashParent h = some p) : h.len = 256 := by
  cases h <;> simp only [hashParent, reduceCtorEq] at hp <;> rfl

theorem hashParent_cases {h p : Name} (hp : hashParent h = some p) :
    h = rh ∨ ∃ v, hashOf v = some h := by
  cases h <;> simp only [hashParent, reduceCtorEq] at hp
  · exact Or.inr ⟨cv _ _, rfl⟩
  · exact Or.inl rfl

theorem hashParent_of_hashOf {v h : Name} (hh : hashOf v = some h) : ∃ p, hashParent h = some p := by
  cases v <;> simp only [hashOf, Option.some.injEq, reduceCtorEq] at hh <;> subst hh <;>
    exact ⟨_, rfl⟩

theorem cost_of_hashOf {v h : Name} (hh : hashOf v = some h) : v.cost = 0 := by
  cases v <;> simp only [hashOf, reduceCtorEq] at hh <;> rfl

theorem prev_zero (k : Fin 41) : prev k 0 = src k := rfl

theorem prev_succ (k : Fin 41) (t : Fin 20) (ht : t.val < 19) :
    prev k ⟨t.val + 1, by omega⟩ = cv k t := by
  simp [prev]

theorem val_rc' (ξ : Rec) : val ξ rc = cat41 fun k => val ξ (cv k 19) := by
  rw [val_rc]
  exact congrArg cat41 (funext fun k => (val_cv ξ k 19).symm)

theorem val_of_hashOf (ξ : Rec) {v h : Name} (hh : hashOf v = some h) :
    trunc (val ξ v) = trunc (ξ.2 h.fin) := by
  cases v <;> simp only [hashOf, Option.some.injEq, reduceCtorEq] at hh <;> subst hh
  rw [val_cv]; exact trunc_128 _

/-! ## The kinds of the nodes -/

theorem graph_kind_hash {h p : Name} (hp : hashParent h = some p) :
    ∃ (hlt : p.fin < h.fin) (hl : graph.len h.fin = paperParams.hashBits),
      graph.kind h.fin = .hash p.fin hlt h.idx hl := by
  rw [graph_kind_fin]
  cases h <;> simp only [hashParent, Option.some.injEq, reduceCtorEq] at hp <;> subst hp <;>
    exact ⟨_, _, rfl⟩

theorem graph_kind_det {n : Name} (hc : n.cost = 0) (hs : ∀ k, n ≠ src k) :
    ∃ (hlt : ∀ w ∈ (Name.parents n).map nameEquiv.toEmbedding, w < n.fin)
      (hf : ∀ x y : Asg, (∀ w ∈ (Name.parents n).map nameEquiv.toEmbedding, x w = y w) →
        (detVal n x).cast (graph_len_fin n).symm = (detVal n y).cast (graph_len_fin n).symm),
      graph.kind n.fin = .det ((Name.parents n).map nameEquiv.toEmbedding) hlt
        (fun x => (detVal n x).cast (graph_len_fin n).symm) hf := by
  rw [graph_kind_fin]
  cases n
  · exact absurd rfl (hs _)
  all_goals first | exact ⟨_, _, rfl⟩ | (simp [Name.cost] at hc)

/-! ## The reconstruction equations in terms of names -/

section Recon

variable {A : Finset Name} {d : Cache paperParams} {given y : graph.Assignment}

theorem yv_mem (hy : graph.ReconEqs d (fins A) given y) {n : Name} (hn : n ∈ A) :
    yv y n = (given n.fin).cast (graph_len_fin n) := by
  unfold yv
  rw [(hy n.fin).1 ((mem_fins A n).mpr hn)]

theorem recon_evaluated (hy : graph.ReconEqs d (fins A) given y) {n : Name}
    (he : Evaluated A n) :
    (∀ p hp τ hl, graph.kind n.fin = .hash p hp τ hl →
        ∃ w, d (.node τ, ⟨graph.len p, y p⟩) = some w ∧ y n.fin = w.cast hl.symm) ∧
      (∀ ps hlt f hf, graph.kind n.fin = .det ps hlt f hf → y n.fin = f y) ∧
      (graph.kind n.fin = .source → y n.fin = 0) :=
  (hy n.fin).2.2 (fun h => he.1 ((mem_fins A n).mp h)) ((visited_iff A n).mpr he.2)

/-- The hash equation at an evaluated hash node. -/
theorem yv_hash (hy : graph.ReconEqs d (fins A) given y) {h p : Name}
    (hp : hashParent h = some p) (he : Evaluated A h) :
    ∃ w, d (.node h.idx, ⟨p.len, yv y p⟩) = some w ∧ trunc w = trunc (yv y h) := by
  obtain ⟨hlt, hl, hk⟩ := graph_kind_hash hp
  obtain ⟨w, hw, hyw⟩ := (recon_evaluated hy he).1 _ _ _ _ hk
  refine ⟨w, ?_, ?_⟩
  · rw [sigma_cast (graph_len_fin p) (y p.fin)] at hw
    exact hw
  · unfold yv
    rw [trunc_cast_eq, hyw, trunc_cast_eq]

/-- The value of an evaluated deterministic node. -/
theorem yv_det (hy : graph.ReconEqs d (fins A) given y) {n : Name} (he : Evaluated A n)
    (hc : n.cost = 0) (hs : ∀ k, n ≠ src k) : yv y n = detVal n y := by
  obtain ⟨hlt, hf, hk⟩ := graph_kind_det hc hs
  have := (recon_evaluated hy he).2.1 _ _ _ _ hk
  unfold yv
  rw [this]
  simp

theorem yv_cv (hy : graph.ReconEqs d (fins A) given y) {k : Fin 41} {t : Fin 20}
    (he : Evaluated A (cv k t)) : yv y (cv k t) = trunc (yv y (ch k t)) := by
  rw [yv_det hy he rfl (by simp)]
  show trunc (y _) = _
  unfold yv
  rw [trunc_cast_eq]

theorem yv_rc (hy : graph.ReconEqs d (fins A) given y) (he : Evaluated A rc) :
    yv y rc = cat41 fun k => yv y (cv k 19) := by
  rw [yv_det hy he rfl (by simp)]
  show cat41 (fun k => trunc (y (cv k 19).fin)) = _
  exact congrArg cat41 (funext fun k => trunc_eq_cast (graph_len_fin (cv k 19)) _)

theorem yv_of_hashOf (hy : graph.ReconEqs d (fins A) given y) {v h : Name}
    (hh : hashOf v = some h) (he : Evaluated A v) : trunc (yv y v) = trunc (yv y h) := by
  cases v <;> simp only [hashOf, Option.some.injEq, reduceCtorEq] at hh <;> subst hh
  rw [yv_cv hy he]; exact trunc_128 _

end Recon

/-! ## The walk -/

/-- One step of the walk through a hash node: `v` feeds the hash node `h`. -/
theorem hash_step {A : Finset Name} (hA : IsCut A) {ξ : Rec} {d : Cache paperParams}
    {given y : graph.Assignment} (hy : graph.ReconEqs d (fins A) given y)
    (hacc : trunc (yv y rh) = pkOf ξ) {v h : Name} (hch : child v = some h)
    (hhp : hashParent h = some v) (hv : ∀ m, Above m v → m ∉ A)
    (hne : yv y v ≠ val ξ v)
    (ih : ∀ v', height v' < height v → (∀ m, Above m v' → m ∉ A) → v'.cost = 0 →
      yv y v' ≠ val ξ v' → Spr d ξ) : Spr d ξ := by
  have h256 : h.len = 256 := len_eq_of_hashParent hhp
  have hhA : h ∉ A := fun hm => by have := hA.values h hm; omega
  have hhE : Evaluated A h := ⟨hhA, fun m hm => hv m (Above.step hch hm)⟩
  obtain ⟨w, hd, hw⟩ := yv_hash hy hhp hhE
  by_cases hsp : trunc w = trunc (ξ.2 h.fin)
  · exact ⟨h, v, hhp, yv y v, hne, w, hd, hsp⟩
  · rcases hashParent_cases hhp with rfl | ⟨v', hv'⟩
    · exfalso
      apply hsp
      rw [hw]
      exact hacc
    · have hcv' : child h = some v' := child_hashOf hv'
      have hv'E : Evaluated A v' :=
        ⟨hv v' (Above.step hch (Above.child hcv')),
          fun m hm => hv m (Above.step hch (Above.step hcv' hm))⟩
      refine ih v' ?_ hv'E.2 (cost_of_hashOf hv') ?_
      · have h1 := height_child hch
        have h2 := height_child hcv'
        omega
      · intro heq
        apply hsp
        rw [hw, ← yv_of_hashOf hy hv' hv'E, heq, val_of_hashOf ξ hv']

/-- **The walk.** -/
theorem up {A : Finset Name} (hA : IsCut A) {ξ : Rec} {d : Cache paperParams}
    {given y : graph.Assignment} (hy : graph.ReconEqs d (fins A) given y)
    (hacc : trunc (yv y rh) = pkOf ξ) {v : Name} (hv : ∀ m, Above m v → m ∉ A)
    (hvh : v.cost = 0) (hne : yv y v ≠ val ξ v) : Spr d ξ := by
  suffices ∀ n, ∀ v, height v = n → (∀ m, Above m v → m ∉ A) → v.cost = 0 →
      yv y v ≠ val ξ v → Spr d ξ from this _ v rfl hv hvh hne
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro v hn hv hvh hne
    have ih' : ∀ v', height v' < height v → (∀ m, Above m v' → m ∉ A) → v'.cost = 0 →
        yv y v' ≠ val ξ v' → Spr d ξ :=
      fun v' hlt => ih (height v') (by omega) v' rfl
    cases v with
    | src k =>
      exact hash_step hA hy hacc (h := ch k 0) rfl rfl hv hne ih'
    | cv k t =>
      by_cases ht : t.val = 19
      · have ht' : t = 19 := Fin.ext ht
        subst ht'
        have hch : child (cv k 19) = some rc := rfl
        have hcE : Evaluated A rc :=
          ⟨hv _ (Above.child hch), fun m hm => hv m (Above.step hch hm)⟩
        refine ih' _ (by have := height_child hch; omega) hcE.2 rfl ?_
        intro heq
        rw [yv_rc hy hcE, val_rc'] at heq
        exact hne (congrFun (cat41_inj heq) k)
      · have hch : child (cv k t) = some (ch k ⟨t.val + 1, by omega⟩) := by simp [Name.child, ht]
        have hhp : hashParent (ch k ⟨t.val + 1, by omega⟩) = some (cv k t) := by
          simp only [hashParent, Option.some.injEq]
          exact prev_succ k t (by omega)
        exact hash_step hA hy hacc hch hhp hv hne ih'
    | rc =>
      exact hash_step hA hy hacc (h := rh) rfl rfl hv hne ih'
    | ch k t => exact absurd hvh (by simp [Name.cost])
    | rh => exact absurd hvh (by simp [Name.cost])

/-! ## The events -/

/-- Signing failed: everything is hidden. -/
theorem events_none {A' : Finset Name} (hA' : IsCut A') {ξ : Rec} {d : Cache paperParams}
    {given y : graph.Assignment} (hy : graph.ReconEqs d (fins A') given y)
    (hacc : trunc (yv y rh) = pkOf ξ) : Spr d ξ ∨ Cache.Hits d (kc ξ) := by
  have hrE : Evaluated A' rh := ⟨hA'.rh_not_mem, fun m hm => absurd hm (not_above_rh m)⟩
  obtain ⟨w, hd, -⟩ := yv_hash hy (p := rc) rfl hrE
  by_cases hne : yv y rc = val ξ rc
  · right
    refine ⟨(.node rh.idx, ⟨rc.len, yv y rc⟩), ?_, by rw [hd]; rfl⟩
    rw [kc_isSome_iff]
    exact ⟨rh, rc, rfl, by rw [hne]; rfl⟩
  · left
    refine up hA' hy hacc (v := rc) ?_ rfl hne
    intro m hm
    rw [above_of_child (show child rc = some rh from rfl)] at hm
    rcases hm with rfl | hm
    · exact hA'.rh_not_mem
    · exact absurd hm (not_above_rh m)

/-- The forgery uses a different disclosure set of the same cost. -/
theorem events_ne {A A' : Finset Name} (hA : IsCut A) (hA' : IsCut A')
    (hcost : ∑ n ∈ evaluatedSet A, n.cost = ∑ n ∈ evaluatedSet A', n.cost) (hne : A ≠ A')
    {ξ : Rec} {d : Cache paperParams} {given y : graph.Assignment}
    (hy : graph.ReconEqs d (fins A') given y) (hacc : trunc (yv y rh) = pkOf ξ) :
    Spr d ξ ∨ Cache.Hits d (fHid (some A) ξ) := by
  obtain ⟨v, hvA, hvE⟩ := exists_mem_evaluated_of_ne hA hA' hcost hne
  have hlen : v.len = 128 := hA.values v hvA
  have hns : ∀ k, v ≠ src k := by
    intro k hk
    subst hk
    rcases hA'.covers k with h | ⟨m, hmA', hm⟩
    · exact hvE.1 h
    · exact hvE.2 m hm hmA'
  obtain ⟨h, hh⟩ := Option.isSome_iff_exists.mp ((hashOf_isSome_iff v).mpr ⟨hlen, hns⟩)
  have hch : child h = some v := child_hashOf hh
  have hhA' : h ∉ A' := fun hm => by
    have := hA'.values h hm
    rw [len_of_hashOf hh] at this
    omega
  have hhE : Evaluated A' h := by
    refine ⟨hhA', fun m hm => ?_⟩
    rw [above_of_child hch] at hm
    rcases hm with rfl | hm
    · exact hvE.1
    · exact hvE.2 m hm
  obtain ⟨p, hhp⟩ := hashParent_of_hashOf hh
  by_cases hvne : yv y v = val ξ v
  · obtain ⟨w, hd, hw⟩ := yv_hash hy hhp hhE
    have htr : trunc w = trunc (ξ.2 h.fin) := by
      rw [hw, ← yv_of_hashOf hy hh hvE, hvne, val_of_hashOf ξ hh]
    by_cases hpne : yv y p = val ξ p
    · right
      refine ⟨(.node h.idx, ⟨p.len, yv y p⟩), ?_, by rw [hd]; rfl⟩
      rw [fHid_isSome_some_iff]
      exact ⟨h, p, hhp, hA.not_evaluated_hashOf hvA hh, by rw [hpne]; rfl⟩
    · left
      exact ⟨h, p, hhp, yv y p, hpne, w, hd, htr⟩
  · left
    exact up hA' hy hacc hvE.2 (cost_of_hashOf hh) hvne

/-- `encode` only reads the values on the set. -/
theorem encode_congr {P : Params} (G : Graph P) (A : Finset (Fin G.size))
    {x x' : G.Assignment} (h : ∀ v ∈ A, x v = x' v) : G.encode A x = G.encode A x' := by
  unfold Graph.encode
  refine List.flatMap_congr fun v hv => ?_
  rw [List.mem_filter, decide_eq_true_iff] at hv
  rw [h v hv.2]

/-- The forgery uses the signed disclosure set with different values. -/
theorem events_same {A : Finset Name} (hA : IsCut A) {ξ : Rec} {d : Cache paperParams}
    {x' : List Bool} {y : graph.Assignment}
    (hy : graph.ReconEqs d (fins A) (graph.decode (fins A) x') y)
    (hacc : trunc (yv y rh) = pkOf ξ) (hlen : x'.length = graph.revealBits (fins A))
    (hne : x' ≠ graph.encode (fins A) (graph.evalRec ξ)) : Spr d ξ := by
  have hex : ∃ a ∈ A, graph.decode (fins A) x' a.fin ≠ graph.evalRec ξ a.fin := by
    by_contra hcon
    push Not at hcon
    apply hne
    rw [← graph.encode_decode (fins A) x' hlen]
    apply encode_congr
    intro v hv
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hv
    exact hcon a ha
  obtain ⟨a, ha, hne'⟩ := hex
  have hcost : a.cost = 0 := cost_eq_zero_of_len (hA.values a ha)
  refine up hA hy hacc (hA.antichain a ha) hcost ?_
  intro heq
  apply hne'
  rw [yv_mem hy ha] at heq
  unfold val at heq
  exact cast_injective _ heq

end Forest

end OptimalOTS
