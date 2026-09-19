import OptimalOTS.WholeWords
import Submissions.ReferenceGenerality1.Names
import Submissions.ReferenceGenerality1.Reconstruct

/-!
# The graph is a whole-word graph

`graph_wholeWords : graph.WholeWords`: the sources have 128 bits, the hashes 256; the tweak words
are constant 128-bit nodes; the hash inputs `ci`, `gc`, `ec`, `rc` concatenate, least significant
first, the value words and then the tweak word; the value nodes `cv`, `gv`, `ev` select the low
half of their hash node.
-/

open OracleSpec OracleComp ENNReal

noncomputable section

open scoped Classical

namespace OptimalOTS

namespace Forest

open Name

/-! ## Bit lists -/

theorem toBits_append {n m : ℕ} (a : BitVec n) (b : BitVec m) :
    toBits (a ++ b) = toBits b ++ toBits a := by
  apply List.ext_getElem
  · simp only [length_toBits, List.length_append]
    omega
  · intro i h1 h2
    rw [length_toBits] at h1
    simp only [toBits, List.getElem_ofFn, BitVec.getLsbD_append, List.getElem_append,
      List.length_ofFn]
    by_cases hi : i < m
    · simp [hi]
    · simp [hi]

theorem toBits_cast {n m : ℕ} (h : n = m) (a : BitVec n) : toBits (a.cast h) = toBits a := by
  subst h; rfl

theorem toBits_trunc {m : ℕ} (h : m = 128) (a : BitVec m) : toBits (trunc a) = toBits a := by
  subst h
  unfold trunc
  rw [BitVec.setWidth_eq]

theorem cast_eq_ofBits {k k' : ℕ} (e : k = k') (a : BitVec k) (L : List Bool)
    (h : toBits a = L) : a.cast e = ofBits k' L := by
  subst e; subst h
  exact (ofBits_toBits a).symm

/-- `ofBits 128` of a longer bit list keeps the low half. -/
theorem ofBits_toBits_eq_trunc {m : ℕ} (a : BitVec m) : ofBits 128 (toBits a) = trunc a := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [ofBits, BitVec.getLsbD_ofNat, trunc, BitVec.getLsbD_setWidth]
  rw [testBit_foldr_bits]
  by_cases him : i < m
  · simp [hi, him, toBits, List.getD_eq_getElem?_getD]
  · simp [hi, him, toBits, List.getD_eq_getElem?_getD, BitVec.getLsbD_of_ge a i (by omega)]

theorem cast_ofBits {k k' : ℕ} (e : k = k') (L : List Bool) : (ofBits k L).cast e = ofBits k' L := by
  subst e; rfl

theorem flatMap_pair {α β : Type} (f : α → List β) (a b : α) : [a, b].flatMap f = f a ++ f b := by
  simp

theorem flatMap_quad {α β : Type} (f : α → List β) (a b c d : α) :
    [a, b, c, d].flatMap f = f a ++ (f b ++ (f c ++ f d)) := by
  simp

theorem flatMap_oct {α β : Type} (f : α → List β) (a b c d e g h i : α) :
    [a, b, c, d, e, g, h, i].flatMap f =
      f a ++ (f b ++ (f c ++ (f d ++ (f e ++ (f g ++ (f h ++ f i)))))) := by
  simp

theorem map_sum_pair {α : Type} (f : α → ℕ) (a b : α) : ([a, b].map f).sum = f a + f b := by
  simp

/-! ## The nodes -/

theorem toBits_trunc_x (x : graph.Assignment) (n : Name) (hn : n.len = 128) :
    toBits (trunc (x n.fin)) = toBits (x n.fin) :=
  toBits_trunc ((graph_len_fin n).trans hn) _

theorem map_parents_ci (k : Fin 63) (t : Fin 14) :
    (Name.parents (ci k t)).map nameEquiv.toEmbedding = [(prev k t).fin, (tc k t).fin].toFinset := by
  ext w
  simp only [Name.parents, Finset.mem_map, Finset.mem_insert, Finset.mem_singleton,
    List.toFinset_cons, List.toFinset_nil, insert_empty_eq]
  constructor
  · rintro ⟨m, hm | hm, rfl⟩ <;> subst hm
    · exact Or.inr rfl
    · exact Or.inl rfl
  · rintro (rfl | rfl)
    · exact ⟨_, Or.inr rfl, rfl⟩
    · exact ⟨_, Or.inl rfl, rfl⟩

theorem map_parents_gc (j : Fin 21) :
    (Name.parents (gc j)).map nameEquiv.toEmbedding =
      [(cv (chainOf j 2) 13).fin, (cv (chainOf j 1) 13).fin, (cv (chainOf j 0) 13).fin,
        (tg j).fin].toFinset := by
  ext w
  simp only [Name.parents, Finset.mem_map, Finset.mem_insert, Finset.mem_singleton,
    List.toFinset_cons, List.toFinset_nil, insert_empty_eq]
  constructor
  · rintro ⟨m, hm | hm | hm | hm, rfl⟩ <;> subst hm <;> simp [nameEquiv]
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨_, Or.inr (Or.inr (Or.inr rfl)), rfl⟩
    · exact ⟨_, Or.inr (Or.inr (Or.inl rfl)), rfl⟩
    · exact ⟨_, Or.inr (Or.inl rfl), rfl⟩
    · exact ⟨_, Or.inl rfl, rfl⟩

theorem map_parents_ec (l : Fin 7) :
    (Name.parents (ec l)).map nameEquiv.toEmbedding =
      [(gv (groupOf l 2)).fin, (gv (groupOf l 1)).fin, (gv (groupOf l 0)).fin,
        (te l).fin].toFinset := by
  ext w
  simp only [Name.parents, Finset.mem_map, Finset.mem_insert, Finset.mem_singleton,
    List.toFinset_cons, List.toFinset_nil, insert_empty_eq]
  constructor
  · rintro ⟨m, hm | hm | hm | hm, rfl⟩ <;> subst hm <;> simp [nameEquiv]
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨_, Or.inr (Or.inr (Or.inr rfl)), rfl⟩
    · exact ⟨_, Or.inr (Or.inr (Or.inl rfl)), rfl⟩
    · exact ⟨_, Or.inr (Or.inl rfl), rfl⟩
    · exact ⟨_, Or.inl rfl, rfl⟩

/-- The words of the root input, least significant first. -/
def rcWords : List (Fin N) :=
  [(ev 6).fin, (ev 5).fin, (ev 4).fin, (ev 3).fin, (ev 2).fin, (ev 1).fin, (ev 0).fin, tr.fin]

theorem map_parents_rc :
    (Name.parents rc).map nameEquiv.toEmbedding = rcWords.toFinset := by
  ext w
  simp only [Name.parents, rcWords, Finset.mem_map, Finset.mem_insert, Finset.mem_image,
    Finset.mem_univ, true_and, List.toFinset_cons, List.toFinset_nil, insert_empty_eq,
    Finset.mem_singleton]
  constructor
  · rintro ⟨m, hm | ⟨l, rfl⟩, rfl⟩
    · subst hm; simp [nameEquiv]
    · fin_cases l <;> simp [nameEquiv]
  · rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    all_goals first
      | exact ⟨_, Or.inl rfl, rfl⟩
      | exact ⟨_, Or.inr ⟨_, rfl⟩, rfl⟩

theorem graph_wholeWords : graph.WholeWords := by
  refine ⟨rfl, fun v => ?_⟩
  obtain ⟨n, rfl⟩ : ∃ n : Name, n.fin = v := ⟨ofFin v, fin_ofFin v⟩
  rw [graph_kind_fin n]
  cases n with
  | src k => exact graph_len_fin _
  | ch k t => trivial
  | gh j => trivial
  | eh l => trivial
  | rh => trivial
  | tc k t => exact Or.inl ⟨Finset.map_empty _, graph_len_fin _⟩
  | tg j => exact Or.inl ⟨Finset.map_empty _, graph_len_fin _⟩
  | te l => exact Or.inl ⟨Finset.map_empty _, graph_len_fin _⟩
  | tr => exact Or.inl ⟨Finset.map_empty _, graph_len_fin _⟩
  | cv k t =>
    refine Or.inr (Or.inr ⟨(ch k t).fin, false, (graph_isHash_fin _).2 (by simp [Name.cost]),
      Finset.map_singleton _ _, graph_len_fin _, fun x => ?_⟩)
    show (trunc (x (ch k t).fin)).cast _ = _
    simp only [Bool.false_eq_true, if_false, List.drop_zero]
    rw [← ofBits_toBits_eq_trunc]
    exact cast_ofBits _ _
  | gv j =>
    refine Or.inr (Or.inr ⟨(gh j).fin, false, (graph_isHash_fin _).2 (by simp [Name.cost]),
      Finset.map_singleton _ _, graph_len_fin _, fun x => ?_⟩)
    show (trunc (x (gh j).fin)).cast _ = _
    simp only [Bool.false_eq_true, if_false, List.drop_zero]
    rw [← ofBits_toBits_eq_trunc]
    exact cast_ofBits _ _
  | ev l =>
    refine Or.inr (Or.inr ⟨(eh l).fin, false, (graph_isHash_fin _).2 (by simp [Name.cost]),
      Finset.map_singleton _ _, graph_len_fin _, fun x => ?_⟩)
    show (trunc (x (eh l).fin)).cast _ = _
    simp only [Bool.false_eq_true, if_false, List.drop_zero]
    rw [← ofBits_toBits_eq_trunc]
    exact cast_ofBits _ _
  | ci k t =>
    refine Or.inr (Or.inl ⟨[(prev k t).fin, (tc k t).fin], map_parents_ci k t, ?_, fun x => ?_⟩)
    · refine ((graph_len_fin (ci k t)).trans ?_).trans (map_sum_pair graph.len _ _).symm
      rw [graph_len_fin, graph_len_fin, Name.len_prev]
      rfl
    · refine cast_eq_ofBits _ _ _ ?_
      show toBits (trunc (x (tc k t).fin) ++ trunc (x (prev k t).fin)) = _
      rw [toBits_append, toBits_trunc_x x (tc k t) rfl, toBits_trunc_x x (prev k t) (Name.len_prev k t)]
      exact (flatMap_pair (fun w => toBits (x w)) _ _).symm
  | gc j =>
    refine Or.inr (Or.inl ⟨_, map_parents_gc j, ?_, fun x => ?_⟩)
    · simp [graph, lenF_fin, Name.len]
    · refine cast_eq_ofBits _ _ _ ?_
      show toBits (trunc (x (tg j).fin) ++ cat3 (trunc (x (cv (chainOf j 0) 13).fin))
        (trunc (x (cv (chainOf j 1) 13).fin)) (trunc (x (cv (chainOf j 2) 13).fin))) = _
      rw [toBits_append, cat3, toBits_cast, toBits_append, toBits_append,
        toBits_trunc_x x _ rfl, toBits_trunc_x x _ rfl, toBits_trunc_x x _ rfl,
        toBits_trunc_x x _ rfl]
      simp only [List.append_assoc]
      exact (flatMap_quad (fun w => toBits (x w)) _ _ _ _).symm
  | ec l =>
    refine Or.inr (Or.inl ⟨_, map_parents_ec l, ?_, fun x => ?_⟩)
    · simp [graph, lenF_fin, Name.len]
    · refine cast_eq_ofBits _ _ _ ?_
      show toBits (trunc (x (te l).fin) ++ cat3 (trunc (x (gv (groupOf l 0)).fin))
        (trunc (x (gv (groupOf l 1)).fin)) (trunc (x (gv (groupOf l 2)).fin))) = _
      rw [toBits_append, cat3, toBits_cast, toBits_append, toBits_append,
        toBits_trunc_x x _ rfl, toBits_trunc_x x _ rfl, toBits_trunc_x x _ rfl,
        toBits_trunc_x x _ rfl]
      simp only [List.append_assoc]
      exact (flatMap_quad (fun w => toBits (x w)) _ _ _ _).symm
  | rc =>
    refine Or.inr (Or.inl ⟨rcWords, map_parents_rc, ?_, fun x => ?_⟩)
    · simp [rcWords, graph, lenF_fin, Name.len]
    · refine cast_eq_ofBits _ _ _ ?_
      show toBits (trunc (x tr.fin) ++ cat7 fun l => trunc (x (ev l).fin)) = _
      rw [toBits_append, cat7, toBits_cast]
      rw [toBits_append, toBits_append, toBits_append, toBits_append, toBits_append,
        toBits_append, toBits_trunc_x x tr rfl, toBits_trunc_x x (ev 0) rfl,
        toBits_trunc_x x (ev 1) rfl, toBits_trunc_x x (ev 2) rfl, toBits_trunc_x x (ev 3) rfl,
        toBits_trunc_x x (ev 4) rfl, toBits_trunc_x x (ev 5) rfl, toBits_trunc_x x (ev 6) rfl]
      simp only [List.append_assoc]
      exact (flatMap_oct (fun w => toBits (x w)) _ _ _ _ _ _ _ _).symm

end Forest

end OptimalOTS
