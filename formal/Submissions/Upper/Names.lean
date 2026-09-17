import OptimalOTS.Statement
import Submissions.Upper.Semantics

/-!
# The concrete scheme: nodes and the computation graph

The scheme of Section 8 of the paper hangs 63 hash chains of length 14 under a tree with 21
group digests, 7 subtree digests and a root.  Every hash node outputs 256 bits; the 128-bit values
of the paper are separate deterministic truncation nodes, and the inputs of the grouping hashes
are separate concatenation nodes.

Nodes are named by `Name`; `Name.fin` embeds the names into `Fin N` in a topological order
(parents first) and `ofFin` is its inverse.

| name | meaning | length | kind |
|---|---|---|---|
| `src k` | source `z_k = c_{k,0}` | 128 | source |
| `ch k t` | `H(τ, c_{k,t})` | 256 | hash, parent `prev k t` |
| `cv k t` | `c_{k,t+1}` = first 128 bits of `ch k t` | 128 | det |
| `gc j` | `c_{3j,14} ‖ c_{3j+1,14} ‖ c_{3j+2,14}` | 384 | det |
| `gh j` | `H(σ_j, gc j)` | 256 | hash |
| `gv j` | `g_j` = first 128 bits of `gh j` | 128 | det |
| `ec l` | `g_{3l} ‖ g_{3l+1} ‖ g_{3l+2}` | 384 | det |
| `eh l` | `H(ρ_l, ec l)` | 256 | hash |
| `ev l` | `e_l` = first 128 bits of `eh l` | 128 | det |
| `rc` | `e_0 ‖ ⋯ ‖ e_6` | 896 | det |
| `rh` | the root `H(τ_r, rc)` | 256 | hash |
-/

open OracleSpec OracleComp ENNReal

noncomputable section

open scoped Classical

namespace OptimalOTS

namespace Forest

/-- Node names. -/
inductive Name where
  | src (k : Fin 63)
  | ch (k : Fin 63) (t : Fin 14)
  | cv (k : Fin 63) (t : Fin 14)
  | gc (j : Fin 21)
  | gh (j : Fin 21)
  | gv (j : Fin 21)
  | ec (l : Fin 7)
  | eh (l : Fin 7)
  | ev (l : Fin 7)
  | rc
  | rh
  deriving DecidableEq

/-- Number of nodes. -/
def N : ℕ := 1913

namespace Name

/-- Topological index. -/
def idx : Name → ℕ
  | src k => k
  | ch k t => 63 + 126 * t + k
  | cv k t => 126 + 126 * t + k
  | gc j => 1827 + j
  | gh j => 1848 + j
  | gv j => 1869 + j
  | ec l => 1890 + l
  | eh l => 1897 + l
  | ev l => 1904 + l
  | rc => 1911
  | rh => 1912

theorem idx_lt (n : Name) : n.idx < N := by
  cases n <;> simp only [idx, N] <;> omega

/-- The index as an element of `Fin N`. -/
def fin (n : Name) : Fin N := ⟨n.idx, n.idx_lt⟩

/-- Output length. -/
def len : Name → ℕ
  | src _ => 128
  | ch _ _ => 256
  | cv _ _ => 128
  | gc _ => 384
  | gh _ => 256
  | gv _ => 128
  | ec _ => 384
  | eh _ => 256
  | ev _ => 128
  | rc => 896
  | rh => 256

/-- Query cost of a node: one compression for every hash node except the root, which costs two. -/
def cost : Name → ℕ
  | ch _ _ => 1
  | gh _ => 1
  | eh _ => 1
  | rh => 2
  | _ => 0

/-- The value node feeding the chain hash `ch k t`: the source for `t = 0`, else `cv k (t-1)`. -/
def prev (k : Fin 63) (t : Fin 14) : Name :=
  if h : t.val = 0 then src k else cv k ⟨t.val - 1, by omega⟩

/-- The `a`-th chain of group `j`. -/
def chainOf (j : Fin 21) (a : Fin 3) : Fin 63 := ⟨3 * j + a, by omega⟩

/-- The `a`-th group of subtree `l`. -/
def groupOf (l : Fin 7) (a : Fin 3) : Fin 21 := ⟨3 * l + a, by omega⟩

/-- The unique node reading the value of a node (`none` for the root). -/
def child : Name → Option Name
  | src k => some (ch k 0)
  | ch k t => some (cv k t)
  | cv k t => if h : t.val = 13 then some (gc ⟨k / 3, by omega⟩) else some (ch k ⟨t + 1, by omega⟩)
  | gc j => some (gh j)
  | gh j => some (gv j)
  | gv j => some (ec ⟨j / 3, by omega⟩)
  | ec l => some (eh l)
  | eh l => some (ev l)
  | ev _ => some rc
  | rc => some rh
  | rh => none

/-- The nodes read by a node. -/
def parents : Name → Finset Name
  | src _ => ∅
  | ch k t => {prev k t}
  | cv k t => {ch k t}
  | gc j => {cv (chainOf j 0) 13, cv (chainOf j 1) 13, cv (chainOf j 2) 13}
  | gh j => {gc j}
  | gv j => {gh j}
  | ec l => {gv (groupOf l 0), gv (groupOf l 1), gv (groupOf l 2)}
  | eh l => {ec l}
  | ev l => {eh l}
  | rc => Finset.univ.image ev
  | rh => {rc}

theorem mem_parents_iff (m n : Name) : m ∈ parents n ↔ child m = some n := by
  cases n <;> cases m <;>
    simp only [parents, child, prev, chainOf, groupOf, Finset.mem_insert, Finset.mem_singleton,
      Finset.mem_image, Finset.mem_univ, true_and, Finset.notMem_empty, Option.some.injEq,
      reduceCtorEq, Name.ch.injEq, Name.cv.injEq, Name.gc.injEq, Name.gh.injEq,
      Name.gv.injEq, Name.ec.injEq, Name.eh.injEq, Name.ev.injEq, Fin.ext_iff,
      Fin.val_zero, iff_true, iff_false, false_iff, or_false, exists_false] <;>
    (try split_ifs) <;>
    (try simp only [Option.some.injEq, reduceCtorEq, Name.src.injEq, Name.ch.injEq, Name.cv.injEq,
      Name.gc.injEq, Fin.ext_iff, iff_false, false_iff, not_false_eq_true]) <;>
    first | omega | exact ⟨_, rfl⟩

theorem idx_lt_of_mem_parents {m n : Name} (h : m ∈ parents n) : m.idx < n.idx := by
  rw [mem_parents_iff] at h
  cases m <;> simp only [child, Option.some.injEq, reduceCtorEq] at h <;>
    (try split_ifs at h) <;> (try simp only [Option.some.injEq] at h) <;> subst h <;>
    simp only [idx, Fin.val_zero] <;> omega

end Name

/-- The inverse of `Name.fin`. -/
def ofFin (v : Fin N) : Name :=
  if h₁ : v.val < 63 then .src ⟨v.val, h₁⟩
  else if h₂ : v.val < 1827 then
    let m := v.val - 63
    let t : Fin 14 := ⟨m / 126, by omega⟩
    let r := m % 126
    if h₃ : r < 63 then .ch ⟨r, h₃⟩ t else .cv ⟨r - 63, by omega⟩ t
  else if h₄ : v.val < 1848 then .gc ⟨v.val - 1827, by omega⟩
  else if h₅ : v.val < 1869 then .gh ⟨v.val - 1848, by omega⟩
  else if h₆ : v.val < 1890 then .gv ⟨v.val - 1869, by omega⟩
  else if h₇ : v.val < 1897 then .ec ⟨v.val - 1890, by omega⟩
  else if h₈ : v.val < 1904 then .eh ⟨v.val - 1897, by omega⟩
  else if h₉ : v.val < 1911 then .ev ⟨v.val - 1904, by omega⟩
  else if h₁₀ : v.val < 1912 then .rc
  else .rh

theorem Name.idx_injective : Function.Injective Name.idx := by
  intro m n h
  cases m <;> cases n <;> simp only [Name.idx] at h <;>
    (try simp only [Name.src.injEq, Name.ch.injEq, Name.cv.injEq, Name.gc.injEq, Name.gh.injEq,
      Name.gv.injEq, Name.ec.injEq, Name.eh.injEq, Name.ev.injEq, Fin.ext_iff, reduceCtorEq]) <;>
    omega

theorem fin_ofFin_aux (v : Fin N) : (ofFin v).fin = v := by
  have hv : v.val < 1913 := v.isLt
  rw [Fin.ext_iff]
  simp only [ofFin]
  split_ifs <;> simp only [Name.fin, Name.idx] <;> omega

theorem ofFin_fin (n : Name) : ofFin n.fin = n :=
  Name.idx_injective (congrArg Fin.val (fin_ofFin_aux n.fin))

theorem fin_ofFin (v : Fin N) : (ofFin v).fin = v := fin_ofFin_aux v

/-- Names and indices. -/
def nameEquiv : Name ≃ Fin N where
  toFun := Name.fin
  invFun := ofFin
  left_inv := ofFin_fin
  right_inv := fin_ofFin

theorem Name.fin_injective : Function.Injective Name.fin := nameEquiv.injective

/-- The finite sum type behind `Name`. -/
abbrev NameSum := Fin 63 ⊕ (Fin 63 × Fin 14) ⊕ (Fin 63 × Fin 14) ⊕ Fin 21 ⊕ Fin 21 ⊕ Fin 21 ⊕
  Fin 7 ⊕ Fin 7 ⊕ Fin 7 ⊕ Unit ⊕ Unit

/-- `Name` as a sum type. -/
def Name.toSum : Name → NameSum
  | src k => .inl k
  | ch k t => .inr (.inl (k, t))
  | cv k t => .inr (.inr (.inl (k, t)))
  | gc j => .inr (.inr (.inr (.inl j)))
  | gh j => .inr (.inr (.inr (.inr (.inl j))))
  | gv j => .inr (.inr (.inr (.inr (.inr (.inl j)))))
  | ec l => .inr (.inr (.inr (.inr (.inr (.inr (.inl l))))))
  | eh l => .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl l)))))))
  | ev l => .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl l))))))))
  | rc => .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl ())))))))))
  | rh => .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr ())))))))))

def Name.ofSum : NameSum → Name
  | .inl k => src k
  | .inr (.inl (k, t)) => ch k t
  | .inr (.inr (.inl (k, t))) => cv k t
  | .inr (.inr (.inr (.inl j))) => gc j
  | .inr (.inr (.inr (.inr (.inl j)))) => gh j
  | .inr (.inr (.inr (.inr (.inr (.inl j))))) => gv j
  | .inr (.inr (.inr (.inr (.inr (.inr (.inl l)))))) => ec l
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl l))))))) => eh l
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl l)))))))) => ev l
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl ()))))))))) => rc
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr ()))))))))) => rh

/-- `Name` is a sum type. -/
def Name.sumEquiv : Name ≃ NameSum where
  toFun := Name.toSum
  invFun := Name.ofSum
  left_inv n := by cases n <;> rfl
  right_inv s := by
    rcases s with k | ⟨k, t⟩ | ⟨k, t⟩ | j | j | j | l | l | l | ⟨⟩ | ⟨⟩ <;> rfl

instance : Fintype Name := Fintype.ofEquiv NameSum Name.sumEquiv.symm

theorem Name.card : Fintype.card Name = N := by
  rw [Fintype.card_congr Name.sumEquiv]
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_unit, N]

/-- Sums over names split by constructor. -/
theorem Name.sum_eq {M : Type} [AddCommMonoid M] (f : Name → M) :
    ∑ n, f n = (∑ k, f (src k)) + (∑ k, ∑ t, f (ch k t)) + (∑ k, ∑ t, f (cv k t)) +
      (∑ j, f (gc j)) + (∑ j, f (gh j)) + (∑ j, f (gv j)) +
      (∑ l, f (ec l)) + (∑ l, f (eh l)) + (∑ l, f (ev l)) + f rc + f rh := by
  rw [← Fintype.sum_equiv Name.sumEquiv.symm (fun s => f (Name.ofSum s)) f (fun _ => rfl)]
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_unique, Name.ofSum,
    add_assoc]

/-! ## The graph -/

/-- Output lengths, indexed by `Fin N`. -/
def lenF (v : Fin N) : ℕ := (ofFin v).len

theorem lenF_fin (n : Name) : lenF n.fin = n.len := by
  rw [lenF, ofFin_fin]

/-- Concatenation of three 128-bit values. -/
def cat3 (a b c : BitVec 128) : BitVec 384 := (a ++ b ++ c).cast (by norm_num)

/-- Concatenation of seven 128-bit values. -/
def cat7 (a : Fin 7 → BitVec 128) : BitVec 896 :=
  (a 0 ++ a 1 ++ a 2 ++ a 3 ++ a 4 ++ a 5 ++ a 6).cast (by norm_num)

/-- The 128-bit truncation. -/
def trunc {w : ℕ} (x : BitVec w) : BitVec 128 := x.setWidth 128

/-- Assignments of the concrete graph. -/
abbrev Asg := (v : Fin N) → BitVec (lenF v)

/-- The deterministic value of a node, as a function of the assignment (only used for the
deterministic nodes; the function is defined on all names for convenience). -/
def detVal (n : Name) (x : Asg) : BitVec n.len :=
  match n with
  | .cv k t => trunc (x (Name.ch k t).fin)
  | .gc j => cat3 (trunc (x (Name.cv (Name.chainOf j 0) 13).fin))
      (trunc (x (Name.cv (Name.chainOf j 1) 13).fin)) (trunc (x (Name.cv (Name.chainOf j 2) 13).fin))
  | .gv j => trunc (x (Name.gh j).fin)
  | .ec l => cat3 (trunc (x (Name.gv (Name.groupOf l 0)).fin))
      (trunc (x (Name.gv (Name.groupOf l 1)).fin)) (trunc (x (Name.gv (Name.groupOf l 2)).fin))
  | .ev l => trunc (x (Name.eh l).fin)
  | .rc => cat7 fun l => trunc (x (Name.ev l).fin)
  | _ => 0

theorem eq_fin_of_ofFin_eq {v : Fin N} {n : Name} (h : ofFin v = n) : v = n.fin := by
  rw [← h, fin_ofFin]

theorem Name.fin_lt_fin_of_mem_parents {m n : Name} (h : m ∈ Name.parents n) : m.fin < n.fin :=
  Name.idx_lt_of_mem_parents h

theorem hash_parent_lt {v : Fin N} {n m : Name} (h : ofFin v = n) (hm : m ∈ Name.parents n) :
    m.fin < v := by
  rw [eq_fin_of_ofFin_eq h]
  exact Name.fin_lt_fin_of_mem_parents hm

theorem det_parents_lt {v : Fin N} {n : Name} (h : ofFin v = n) :
    ∀ w ∈ (Name.parents n).map nameEquiv.toEmbedding, w < v := by
  intro w hw
  rw [Finset.mem_map] at hw
  obtain ⟨m, hm, rfl⟩ := hw
  exact hash_parent_lt h hm

theorem detVal_local (n : Name) (x y : Asg)
    (hxy : ∀ w ∈ (Name.parents n).map nameEquiv.toEmbedding, x w = y w) :
    detVal n x = detVal n y := by
  have key : ∀ m ∈ Name.parents n, x m.fin = y m.fin := fun m hm =>
    hxy m.fin (Finset.mem_map_of_mem _ hm)
  cases n with
  | cv k t =>
    show trunc (x (Name.ch k t).fin) = trunc (y (Name.ch k t).fin)
    rw [key (Name.ch k t) (by simp [Name.parents])]
  | gc j =>
    show cat3 (trunc (x (Name.cv (Name.chainOf j 0) 13).fin))
        (trunc (x (Name.cv (Name.chainOf j 1) 13).fin))
        (trunc (x (Name.cv (Name.chainOf j 2) 13).fin)) =
      cat3 (trunc (y (Name.cv (Name.chainOf j 0) 13).fin))
        (trunc (y (Name.cv (Name.chainOf j 1) 13).fin))
        (trunc (y (Name.cv (Name.chainOf j 2) 13).fin))
    rw [key (Name.cv (Name.chainOf j 0) 13) (by simp [Name.parents]),
      key (Name.cv (Name.chainOf j 1) 13) (by simp [Name.parents]),
      key (Name.cv (Name.chainOf j 2) 13) (by simp [Name.parents])]
  | gv j =>
    show trunc (x (Name.gh j).fin) = trunc (y (Name.gh j).fin)
    rw [key (Name.gh j) (by simp [Name.parents])]
  | ec l =>
    show cat3 (trunc (x (Name.gv (Name.groupOf l 0)).fin))
        (trunc (x (Name.gv (Name.groupOf l 1)).fin))
        (trunc (x (Name.gv (Name.groupOf l 2)).fin)) =
      cat3 (trunc (y (Name.gv (Name.groupOf l 0)).fin))
        (trunc (y (Name.gv (Name.groupOf l 1)).fin))
        (trunc (y (Name.gv (Name.groupOf l 2)).fin))
    rw [key (Name.gv (Name.groupOf l 0)) (by simp [Name.parents]),
      key (Name.gv (Name.groupOf l 1)) (by simp [Name.parents]),
      key (Name.gv (Name.groupOf l 2)) (by simp [Name.parents])]
  | ev l =>
    show trunc (x (Name.eh l).fin) = trunc (y (Name.eh l).fin)
    rw [key (Name.eh l) (by simp [Name.parents])]
  | rc =>
    show cat7 (fun l => trunc (x (Name.ev l).fin)) = cat7 (fun l => trunc (y (Name.ev l).fin))
    congr 1
    funext l
    rw [key (Name.ev l) (Finset.mem_image_of_mem _ (Finset.mem_univ _))]
  | src _ => rfl
  | ch _ _ => rfl
  | gh _ => rfl
  | eh _ => rfl
  | rh => rfl

/-- The kind of the node `v = n.fin`. -/
def kindOf (v : Fin N) : (n : Name) → ofFin v = n → NodeKind 256 N lenF v
  | .src _, _ => .source
  | .ch k t, h => .hash (Name.prev k t).fin
      (by exact hash_parent_lt h (Finset.mem_singleton_self _)) v.val (by rw [lenF, h]; rfl)
  | .cv k t, h => .det ((Name.parents (.cv k t)).map nameEquiv.toEmbedding)
      (by exact det_parents_lt h)
      (fun x => (detVal (.cv k t) x).cast (by rw [lenF, h]))
      (by intro x y hxy; exact congrArg _ (detVal_local _ x y hxy))
  | .gc j, h => .det ((Name.parents (.gc j)).map nameEquiv.toEmbedding)
      (by exact det_parents_lt h)
      (fun x => (detVal (.gc j) x).cast (by rw [lenF, h]))
      (by intro x y hxy; exact congrArg _ (detVal_local _ x y hxy))
  | .gh j, h => .hash (Name.gc j).fin
      (by exact hash_parent_lt h (Finset.mem_singleton_self _)) v.val (by rw [lenF, h]; rfl)
  | .gv j, h => .det ((Name.parents (.gv j)).map nameEquiv.toEmbedding)
      (by exact det_parents_lt h)
      (fun x => (detVal (.gv j) x).cast (by rw [lenF, h]))
      (by intro x y hxy; exact congrArg _ (detVal_local _ x y hxy))
  | .ec l, h => .det ((Name.parents (.ec l)).map nameEquiv.toEmbedding)
      (by exact det_parents_lt h)
      (fun x => (detVal (.ec l) x).cast (by rw [lenF, h]))
      (by intro x y hxy; exact congrArg _ (detVal_local _ x y hxy))
  | .eh l, h => .hash (Name.ec l).fin
      (by exact hash_parent_lt h (Finset.mem_singleton_self _)) v.val (by rw [lenF, h]; rfl)
  | .ev l, h => .det ((Name.parents (.ev l)).map nameEquiv.toEmbedding)
      (by exact det_parents_lt h)
      (fun x => (detVal (.ev l) x).cast (by rw [lenF, h]))
      (by intro x y hxy; exact congrArg _ (detVal_local _ x y hxy))
  | .rc, h => .det ((Name.parents .rc).map nameEquiv.toEmbedding)
      (by exact det_parents_lt h)
      (fun x => (detVal .rc x).cast (by rw [lenF, h]))
      (by intro x y hxy; exact congrArg _ (detVal_local _ x y hxy))
  | .rh, h => .hash Name.rc.fin
      (by exact hash_parent_lt h (Finset.mem_singleton_self _)) v.val (by rw [lenF, h]; rfl)

theorem kindOf_isHash (v : Fin N) (n : Name) (h : ofFin v = n) :
    (kindOf v n h).IsHash ↔ n.cost ≠ 0 := by
  cases n <;> simp [kindOf, NodeKind.IsHash, Name.cost]

theorem kindOf_isSource (v : Fin N) (n : Name) (h : ofFin v = n) :
    (kindOf v n h).IsSource ↔ ∃ k, n = .src k := by
  cases n <;> simp [kindOf, NodeKind.IsSource]

theorem kindOf_parents (v : Fin N) (n : Name) (h : ofFin v = n) :
    (kindOf v n h).parents = (Name.parents n).map nameEquiv.toEmbedding := by
  cases n <;> simp [kindOf, NodeKind.parents, Name.parents, nameEquiv]

theorem kindOf_label (v : Fin N) (n : Name) (h : ofFin v = n) (τ : ℕ)
    (hτ : (kindOf v n h).label? = some τ) : τ = v.val := by
  cases n <;> simp [kindOf, NodeKind.label?] at hτ <;> omega

/-- The computation graph of the scheme. -/
def graph : Graph paperParams where
  size := N
  len := lenF
  kind v := kindOf v (ofFin v) rfl
  root := Name.rh.fin
  root_isHash := (kindOf_isHash _ _ rfl).2 (by rw [ofFin_fin]; decide)
  label_injective := fun v w τ hv hw =>
    Fin.ext ((kindOf_label _ _ _ _ hv).symm.trans (kindOf_label _ _ _ _ hw))

theorem graph_kind_eq (v : Fin N) (n : Name) (h : ofFin v = n) : graph.kind v = kindOf v n h := by
  subst h; rfl

theorem graph_kind_fin (n : Name) : graph.kind n.fin = kindOf n.fin n (ofFin_fin n) :=
  graph_kind_eq _ _ _

theorem graph_size : graph.size = N := rfl

theorem graph_len_fin (n : Name) : graph.len n.fin = n.len := lenF_fin n

/-- The parents of a node, in the graph. -/
theorem graph_parents_fin (n : Name) :
    (graph.kind n.fin).parents = (Name.parents n).map nameEquiv.toEmbedding := by
  rw [graph_kind_fin]; exact kindOf_parents _ _ _

theorem graph_isHash_fin (n : Name) :
    (graph.kind n.fin).IsHash ↔ n.cost ≠ 0 := by
  rw [graph_kind_fin]; exact kindOf_isHash _ _ _

theorem graph_isSource_fin (n : Name) :
    (graph.kind n.fin).IsSource ↔ ∃ k, n = .src k := by
  rw [graph_kind_fin]; exact kindOf_isSource _ _ _

theorem Name.len_prev (k : Fin 63) (t : Fin 14) : (Name.prev k t).len = 128 := by
  unfold Name.prev; split_ifs <;> rfl

theorem graph_nodeCost_fin (n : Name) : graph.nodeCost n.fin = n.cost := by
  unfold Graph.nodeCost
  rw [graph_kind_fin]
  cases n <;> simp only [kindOf, graph_len_fin, Name.len_prev] <;>
    simp [Name.cost, Name.len, blockCost, paperParams]

theorem graph_keygenCost : graph.keygenCost = 912 := by
  show ∑ v : Fin N, graph.nodeCost v = 912
  rw [← Fintype.sum_equiv nameEquiv (fun n => graph.nodeCost n.fin) (fun v => graph.nodeCost v)
    (fun _ => rfl)]
  simp only [graph_nodeCost_fin]
  rw [Name.sum_eq]
  simp [Name.cost]

end Forest

end OptimalOTS
