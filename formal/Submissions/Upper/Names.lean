import OptimalOTS.Statement
import Submissions.Upper.Semantics

/-!
# The concrete scheme: nodes and the computation graph

The scheme hangs 41 hash chains of length 20 directly under the root.  Every hash node outputs
256 bits; the 128-bit values are separate deterministic truncation nodes, and the input of the
root hash is a separate concatenation node of the 41 chain ends (5248 bits).

Nodes are named by `Name`; `Name.fin` embeds the names into `Fin N` in a topological order
(parents first) and `ofFin` is its inverse.

| name | meaning | length | kind | cost |
|---|---|---|---|---|
| `src k` | source `z_k = c_{k,0}` | 128 | source | 0 |
| `ch k t` | `H(τ, c_{k,t})` | 256 | hash, parent `prev k t` | 1 |
| `cv k t` | `c_{k,t+1}` = first 128 bits of `ch k t` | 128 | det | 0 |
| `rc` | `c_{0,20} ‖ ⋯ ‖ c_{40,20}` | 5248 | det | 0 |
| `rh` | the root `H(τ_r, rc)` | 256 | hash | 11 |

Costs follow the contract: one unit per started 512-bit block of the input plus 192 overhead
bits, so a chain hash (128 bits) costs one unit and the root (5248 bits) costs eleven.
-/

open OracleSpec OracleComp ENNReal

noncomputable section

open scoped Classical

namespace OptimalOTS

namespace Forest

/-- Node names. -/
inductive Name where
  | src (k : Fin 41)
  | ch (k : Fin 41) (t : Fin 20)
  | cv (k : Fin 41) (t : Fin 20)
  | rc
  | rh
  deriving DecidableEq

/-- Number of nodes. -/
def N : ℕ := 1683

namespace Name

/-- Topological index. -/
def idx : Name → ℕ
  | src k => k
  | ch k t => 41 + 82 * t + k
  | cv k t => 82 + 82 * t + k
  | rc => 1681
  | rh => 1682

theorem idx_lt (n : Name) : n.idx < N := by
  cases n <;> simp only [idx, N] <;> omega

/-- The index as an element of `Fin N`. -/
def fin (n : Name) : Fin N := ⟨n.idx, n.idx_lt⟩

/-- Output length. -/
def len : Name → ℕ
  | src _ => 128
  | ch _ _ => 256
  | cv _ _ => 128
  | rc => 5248
  | rh => 256

/-- Query cost of a node: one unit for a chain hash, eleven for the root. -/
def cost : Name → ℕ
  | ch _ _ => 1
  | rh => 11
  | _ => 0

/-- The value node feeding the chain hash `ch k t`: the source for `t = 0`, else `cv k (t-1)`. -/
def prev (k : Fin 41) (t : Fin 20) : Name :=
  if h : t.val = 0 then src k else cv k ⟨t.val - 1, by omega⟩

/-- The unique node reading the value of a node (`none` for the root). -/
def child : Name → Option Name
  | src k => some (ch k 0)
  | ch k t => some (cv k t)
  | cv k t => if h : t.val = 19 then some rc else some (ch k ⟨t + 1, by omega⟩)
  | rc => some rh
  | rh => none

/-- The nodes read by a node. -/
def parents : Name → Finset Name
  | src _ => ∅
  | ch k t => {prev k t}
  | cv k t => {ch k t}
  | rc => Finset.univ.image fun k => cv k 19
  | rh => {rc}

theorem mem_parents_iff (m n : Name) : m ∈ parents n ↔ child m = some n := by
  cases n <;> cases m <;>
    simp only [parents, child, prev, Finset.mem_singleton, Finset.mem_image, Finset.mem_univ,
      true_and, Finset.notMem_empty, Option.some.injEq, reduceCtorEq, Name.src.injEq,
      Name.ch.injEq, Name.cv.injEq, exists_eq_left, exists_false, false_iff, iff_false,
      not_false_eq_true] <;>
    (try split_ifs) <;>
    (try simp only [Option.some.injEq, reduceCtorEq, Name.src.injEq, Name.ch.injEq, Name.cv.injEq,
      Fin.ext_iff, Fin.val_zero, Fin.isValue, iff_true, iff_false, false_iff, true_iff,
      not_false_eq_true, not_and, and_true, true_and, and_comm]) <;>
    (try omega)

theorem idx_lt_of_mem_parents {m n : Name} (h : m ∈ parents n) : m.idx < n.idx := by
  rw [mem_parents_iff] at h
  cases m <;> simp only [child, Option.some.injEq, reduceCtorEq] at h <;>
    (try split_ifs at h) <;> (try simp only [Option.some.injEq] at h) <;> subst h <;>
    simp only [idx, Fin.val_zero] <;> omega

end Name

/-- The inverse of `Name.fin`. -/
def ofFin (v : Fin N) : Name :=
  if h₁ : v.val < 41 then .src ⟨v.val, h₁⟩
  else if h₂ : v.val < 1681 then
    let m := v.val - 41
    let t : Fin 20 := ⟨m / 82, by omega⟩
    let r := m % 82
    if h₃ : r < 41 then .ch ⟨r, h₃⟩ t else .cv ⟨r - 41, by omega⟩ t
  else if h₄ : v.val < 1682 then .rc
  else .rh

theorem Name.idx_injective : Function.Injective Name.idx := by
  intro m n h
  cases m <;> cases n <;> simp only [Name.idx] at h <;>
    (try simp only [Name.src.injEq, Name.ch.injEq, Name.cv.injEq, Fin.ext_iff, reduceCtorEq]) <;>
    omega

theorem fin_ofFin_aux (v : Fin N) : (ofFin v).fin = v := by
  have hv : v.val < 1683 := v.isLt
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
abbrev NameSum := Fin 41 ⊕ (Fin 41 × Fin 20) ⊕ (Fin 41 × Fin 20) ⊕ Unit ⊕ Unit

/-- `Name` as a sum type. -/
def Name.toSum : Name → NameSum
  | src k => .inl k
  | ch k t => .inr (.inl (k, t))
  | cv k t => .inr (.inr (.inl (k, t)))
  | rc => .inr (.inr (.inr (.inl ())))
  | rh => .inr (.inr (.inr (.inr ())))

def Name.ofSum : NameSum → Name
  | .inl k => src k
  | .inr (.inl (k, t)) => ch k t
  | .inr (.inr (.inl (k, t))) => cv k t
  | .inr (.inr (.inr (.inl ()))) => rc
  | .inr (.inr (.inr (.inr ()))) => rh

/-- `Name` is a sum type. -/
def Name.sumEquiv : Name ≃ NameSum where
  toFun := Name.toSum
  invFun := Name.ofSum
  left_inv n := by cases n <;> rfl
  right_inv s := by
    rcases s with k | ⟨k, t⟩ | ⟨k, t⟩ | ⟨⟩ | ⟨⟩ <;> rfl

instance : Fintype Name := Fintype.ofEquiv NameSum Name.sumEquiv.symm

theorem Name.card : Fintype.card Name = N := by
  rw [Fintype.card_congr Name.sumEquiv]
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_unit, N]

/-- Sums over names split by constructor. -/
theorem Name.sum_eq {M : Type} [AddCommMonoid M] (f : Name → M) :
    ∑ n, f n = (∑ k, f (src k)) + (∑ k, ∑ t, f (ch k t)) + (∑ k, ∑ t, f (cv k t)) + f rc + f rh := by
  rw [← Fintype.sum_equiv Name.sumEquiv.symm (fun s => f (Name.ofSum s)) f (fun _ => rfl)]
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_unique, Name.ofSum,
    add_assoc]

/-! ## The graph -/

/-- Output lengths, indexed by `Fin N`. -/
def lenF (v : Fin N) : ℕ := (ofFin v).len

theorem lenF_fin (n : Name) : lenF n.fin = n.len := by
  rw [lenF, ofFin_fin]

/-- Concatenation of `n` 128-bit values, first value in the high bits. -/
def catN : (n : ℕ) → (Fin n → BitVec 128) → BitVec (128 * n)
  | 0, _ => (BitVec.nil).cast (by simp)
  | n + 1, a => ((catN n fun i => a i.castSucc) ++ a (Fin.last n)).cast (by ring)

/-- Concatenation of the 41 chain ends. -/
def cat41 (a : Fin 41 → BitVec 128) : BitVec 5248 := (catN 41 a).cast (by norm_num)

/-- The 128-bit truncation. -/
def trunc {w : ℕ} (x : BitVec w) : BitVec 128 := x.setWidth 128

/-- Assignments of the concrete graph. -/
abbrev Asg := (v : Fin N) → BitVec (lenF v)

/-- The deterministic value of a node, as a function of the assignment (only used for the
deterministic nodes; the function is defined on all names for convenience). -/
def detVal (n : Name) (x : Asg) : BitVec n.len :=
  match n with
  | .cv k t => trunc (x (Name.ch k t).fin)
  | .rc => cat41 fun k => trunc (x (Name.cv k 19).fin)
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
  | rc =>
    show cat41 (fun k => trunc (x (Name.cv k 19).fin)) = cat41 (fun k => trunc (y (Name.cv k 19).fin))
    congr 1
    funext k
    rw [key (Name.cv k 19) (Finset.mem_image_of_mem _ (Finset.mem_univ _))]
  | src _ => rfl
  | ch _ _ => rfl
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

theorem Name.len_prev (k : Fin 41) (t : Fin 20) : (Name.prev k t).len = 128 := by
  unfold Name.prev; split_ifs <;> rfl

theorem graph_nodeCost_fin (n : Name) : graph.nodeCost n.fin = n.cost := by
  unfold Graph.nodeCost
  rw [graph_kind_fin]
  cases n <;> simp only [kindOf, graph_len_fin, Name.len_prev] <;>
    simp [Name.cost, Name.len, blockCost, paperParams]

theorem graph_keygenCost : graph.keygenCost = 831 := by
  show ∑ v : Fin N, graph.nodeCost v = 831
  rw [← Fintype.sum_equiv nameEquiv (fun n => graph.nodeCost n.fin) (fun v => graph.nodeCost v)
    (fun _ => rfl)]
  simp only [graph_nodeCost_fin]
  rw [Name.sum_eq]
  simp [Name.cost]

end Forest

end OptimalOTS
