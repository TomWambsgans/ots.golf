import OptimalOTS.Statement
import Submissions.WholeWordsUpper.Semantics

/-!
# The concrete scheme: nodes and the computation graph

The scheme of Section 8 of the paper hangs 63 hash chains of length 14 under a tree with 21
group digests, 7 subtree digests and a root.  Every hash node outputs 256 bits; the 128-bit values
of the paper are separate nodes selecting the low half of a hash node, and the inputs of the hash
nodes are separate concatenation nodes.  Every value consists of whole 128-bit words.

Nodes are named by `Name`; `Name.fin` embeds the names into `Fin N` in a topological order
(parents first) and `ofFin` is its inverse.

The random oracle has no labels, so the scheme separates its hash nodes itself: the input of the
hash node `h` starts with the 128-bit tweak word `tw h` (the index of `h`), in the high bits,
i.e. it is `tw h ++ payload`.  The tweak word is a public constant node of its own (one per hash
node, with the hash input as its only child).

| name | meaning | length | kind |
|---|---|---|---|
| `tc k t`, `tg j`, `te l`, `tr` | the tweak words `tw (ch k t)`, `tw (gh j)`, `tw (eh l)`, `tw rh` | 128 | det, constant |
| `src k` | source `z_k = c_{k,0}` | 128 | source |
| `ci k t` | `tw (ch k t) ‖ c_{k,t}`, the input of `ch k t` | 256 | det, concatenation |
| `ch k t` | `H(ci k t)` | 256 | hash |
| `cv k t` | `c_{k,t+1}` = low half of `ch k t` | 128 | det, half |
| `gc j` | `tw (gh j) ‖ c_{3j,14} ‖ c_{3j+1,14} ‖ c_{3j+2,14}` | 512 | det, concatenation |
| `gh j` | `H(gc j)` | 256 | hash |
| `gv j` | `g_j` = low half of `gh j` | 128 | det, half |
| `ec l` | `tw (eh l) ‖ g_{3l} ‖ g_{3l+1} ‖ g_{3l+2}` | 512 | det, concatenation |
| `eh l` | `H(ec l)` | 256 | hash |
| `ev l` | `e_l` = low half of `eh l` | 128 | det, half |
| `rc` | `tw rh ‖ e_0 ‖ ⋯ ‖ e_6` | 1024 | det, concatenation |
| `rh` | the root `H(rc)` | 256 | hash |
-/

open OracleSpec OracleComp ENNReal

noncomputable section

open scoped Classical

namespace OptimalOTS

namespace Forest

/-- Node names. -/
inductive Name where
  | src (k : Fin 63)
  | ci (k : Fin 63) (t : Fin 14)
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
  | tc (k : Fin 63) (t : Fin 14)
  | tg (j : Fin 21)
  | te (l : Fin 7)
  | tr
  deriving DecidableEq

/-- Number of nodes. -/
def N : ℕ := 3706

namespace Name

/-- Topological index: the tweak words first, then the nodes of the forest. -/
def idx : Name → ℕ
  | tc k t => 63 * t + k
  | tg j => 882 + j
  | te l => 903 + l
  | tr => 910
  | src k => 911 + k
  | ci k t => 974 + 189 * t + k
  | ch k t => 1037 + 189 * t + k
  | cv k t => 1100 + 189 * t + k
  | gc j => 3620 + j
  | gh j => 3641 + j
  | gv j => 3662 + j
  | ec l => 3683 + l
  | eh l => 3690 + l
  | ev l => 3697 + l
  | rc => 3704
  | rh => 3705

theorem idx_lt (n : Name) : n.idx < N := by
  cases n <;> simp only [idx, N] <;> omega

/-- The index as an element of `Fin N`. -/
def fin (n : Name) : Fin N := ⟨n.idx, n.idx_lt⟩

/-- Output length. -/
def len : Name → ℕ
  | src _ => 128
  | ci _ _ => 256
  | ch _ _ => 256
  | cv _ _ => 128
  | gc _ => 512
  | gh _ => 256
  | gv _ => 128
  | ec _ => 512
  | eh _ => 256
  | ev _ => 128
  | rc => 1024
  | rh => 256
  | tc _ _ => 128
  | tg _ => 128
  | te _ => 128
  | tr => 128

/-- Query cost of a node: one compression for every hash node except the root, which costs two. -/
def cost : Name → ℕ
  | ch _ _ => 1
  | gh _ => 1
  | eh _ => 1
  | rh => 2
  | _ => 0

/-- The tweak words. -/
def isTw : Name → Bool
  | tc _ _ => true
  | tg _ => true
  | te _ => true
  | tr => true
  | _ => false

/-- The tweak word of a hash node (junk for other nodes). -/
def twOf : Name → Name
  | ch k t => tc k t
  | gh j => tg j
  | eh l => te l
  | rh => tr
  | n => n

/-- The value node feeding the chain hash `ch k t` (through its input `ci k t`): the source for
`t = 0`, else `cv k (t-1)`. -/
def prev (k : Fin 63) (t : Fin 14) : Name :=
  if h : t.val = 0 then src k else cv k ⟨t.val - 1, by omega⟩

/-- The `a`-th chain of group `j`. -/
def chainOf (j : Fin 21) (a : Fin 3) : Fin 63 := ⟨3 * j + a, by omega⟩

/-- The `a`-th group of subtree `l`. -/
def groupOf (l : Fin 7) (a : Fin 3) : Fin 21 := ⟨3 * l + a, by omega⟩

/-- The unique node reading the value of a node (`none` for the root). -/
def child : Name → Option Name
  | src k => some (ci k 0)
  | ci k t => some (ch k t)
  | ch k t => some (cv k t)
  | cv k t => if h : t.val = 13 then some (gc ⟨k / 3, by omega⟩) else some (ci k ⟨t + 1, by omega⟩)
  | gc j => some (gh j)
  | gh j => some (gv j)
  | gv j => some (ec ⟨j / 3, by omega⟩)
  | ec l => some (eh l)
  | eh l => some (ev l)
  | ev _ => some rc
  | rc => some rh
  | rh => none
  | tc k t => some (ci k t)
  | tg j => some (gc j)
  | te l => some (ec l)
  | tr => some rc

/-- The nodes read by a node. -/
def parents : Name → Finset Name
  | src _ => ∅
  | ci k t => {tc k t, prev k t}
  | ch k t => {ci k t}
  | cv k t => {ch k t}
  | gc j => {tg j, cv (chainOf j 0) 13, cv (chainOf j 1) 13, cv (chainOf j 2) 13}
  | gh j => {gc j}
  | gv j => {gh j}
  | ec l => {te l, gv (groupOf l 0), gv (groupOf l 1), gv (groupOf l 2)}
  | eh l => {ec l}
  | ev l => {eh l}
  | rc => insert tr (Finset.univ.image ev)
  | rh => {rc}
  | tc _ _ => ∅
  | tg _ => ∅
  | te _ => ∅
  | tr => ∅

theorem mem_parents_iff (m n : Name) : m ∈ parents n ↔ child m = some n := by
  cases n <;> cases m <;>
    simp only [parents, child, prev, chainOf, groupOf, Finset.mem_insert, Finset.mem_singleton,
      Finset.mem_image, Finset.mem_univ, true_and, Finset.notMem_empty, Option.some.injEq,
      reduceCtorEq, Name.ci.injEq, Name.ch.injEq, Name.cv.injEq, Name.gc.injEq, Name.gh.injEq,
      Name.gv.injEq, Name.ec.injEq, Name.eh.injEq, Name.ev.injEq, Name.tc.injEq, Name.tg.injEq,
      Name.te.injEq, Fin.ext_iff,
      Fin.val_zero, iff_true, iff_false, false_iff, or_false, false_or, exists_false] <;>
    (try split_ifs) <;>
    (try simp only [Option.some.injEq, reduceCtorEq, Name.src.injEq, Name.ci.injEq,
      Name.cv.injEq, Name.gc.injEq, Fin.ext_iff, iff_false, false_iff, not_false_eq_true]) <;>
    first | omega | exact ⟨_, rfl⟩ | tauto

theorem idx_lt_of_mem_parents {m n : Name} (h : m ∈ parents n) : m.idx < n.idx := by
  rw [mem_parents_iff] at h
  cases m <;> simp only [child, Option.some.injEq, reduceCtorEq] at h <;>
    (try split_ifs at h) <;> (try simp only [Option.some.injEq] at h) <;> subst h <;>
    simp only [idx, Fin.val_zero] <;> omega

end Name

/-- The inverse of `Name.fin`. -/
def ofFin (v : Fin N) : Name :=
  if h₀ : v.val < 882 then .tc ⟨v.val % 63, by omega⟩ ⟨v.val / 63, by omega⟩
  else if h₀₁ : v.val < 903 then .tg ⟨v.val - 882, by omega⟩
  else if h₀₂ : v.val < 910 then .te ⟨v.val - 903, by omega⟩
  else if h₀₃ : v.val < 911 then .tr
  else if h₁ : v.val < 974 then .src ⟨v.val - 911, by omega⟩
  else if h₂ : v.val < 3620 then
    let m := v.val - 974
    let t : Fin 14 := ⟨m / 189, by omega⟩
    let r := m % 189
    if h₃ : r < 63 then .ci ⟨r, h₃⟩ t
    else if h₃' : r < 126 then .ch ⟨r - 63, by omega⟩ t
    else .cv ⟨r - 126, by omega⟩ t
  else if h₄ : v.val < 3641 then .gc ⟨v.val - 3620, by omega⟩
  else if h₅ : v.val < 3662 then .gh ⟨v.val - 3641, by omega⟩
  else if h₆ : v.val < 3683 then .gv ⟨v.val - 3662, by omega⟩
  else if h₇ : v.val < 3690 then .ec ⟨v.val - 3683, by omega⟩
  else if h₈ : v.val < 3697 then .eh ⟨v.val - 3690, by omega⟩
  else if h₉ : v.val < 3704 then .ev ⟨v.val - 3697, by omega⟩
  else if h₁₀ : v.val < 3705 then .rc
  else .rh

theorem Name.idx_injective : Function.Injective Name.idx := by
  intro m n h
  cases m <;> cases n <;> simp only [Name.idx] at h <;>
    (try simp only [Name.src.injEq, Name.ci.injEq, Name.ch.injEq, Name.cv.injEq, Name.gc.injEq,
      Name.gh.injEq, Name.gv.injEq, Name.ec.injEq, Name.eh.injEq, Name.ev.injEq, Name.tc.injEq,
      Name.tg.injEq, Name.te.injEq, Fin.ext_iff, reduceCtorEq]) <;>
    omega

theorem idx_ofFin (v : Fin N) : (ofFin v).idx = v.val := by
  obtain ⟨v, hv⟩ := v
  unfold N at hv
  unfold ofFin
  dsimp only
  by_cases h0 : v < 882
  · rw [dif_pos h0]; simp only [Name.idx]; omega
  rw [dif_neg h0]
  by_cases h1 : v < 903
  · rw [dif_pos h1]; simp only [Name.idx]; omega
  rw [dif_neg h1]
  by_cases h2 : v < 910
  · rw [dif_pos h2]; simp only [Name.idx]; omega
  rw [dif_neg h2]
  by_cases h3 : v < 911
  · rw [dif_pos h3]; simp only [Name.idx]; omega
  rw [dif_neg h3]
  by_cases h4 : v < 974
  · rw [dif_pos h4]; simp only [Name.idx]; omega
  rw [dif_neg h4]
  by_cases h5 : v < 3620
  · rw [dif_pos h5]
    by_cases ha : (v - 974) % 189 < 63
    · rw [dif_pos ha]; simp only [Name.idx]; omega
    rw [dif_neg ha]
    by_cases hb : (v - 974) % 189 < 126
    · rw [dif_pos hb]; simp only [Name.idx]; omega
    rw [dif_neg hb]; simp only [Name.idx]; omega
  rw [dif_neg h5]
  by_cases h6 : v < 3641
  · rw [dif_pos h6]; simp only [Name.idx]; omega
  rw [dif_neg h6]
  by_cases h7 : v < 3662
  · rw [dif_pos h7]; simp only [Name.idx]; omega
  rw [dif_neg h7]
  by_cases h8 : v < 3683
  · rw [dif_pos h8]; simp only [Name.idx]; omega
  rw [dif_neg h8]
  by_cases h9 : v < 3690
  · rw [dif_pos h9]; simp only [Name.idx]; omega
  rw [dif_neg h9]
  by_cases h10 : v < 3697
  · rw [dif_pos h10]; simp only [Name.idx]; omega
  rw [dif_neg h10]
  by_cases h11 : v < 3704
  · rw [dif_pos h11]; simp only [Name.idx]; omega
  rw [dif_neg h11]
  by_cases h12 : v < 3705
  · rw [dif_pos h12]; simp only [Name.idx]; omega
  rw [dif_neg h12]
  simp only [Name.idx]; omega

theorem fin_ofFin_aux (v : Fin N) : (ofFin v).fin = v := Fin.ext (idx_ofFin v)

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
abbrev NameSum := Fin 63 ⊕ (Fin 63 × Fin 14) ⊕ (Fin 63 × Fin 14) ⊕ (Fin 63 × Fin 14) ⊕
  Fin 21 ⊕ Fin 21 ⊕ Fin 21 ⊕ Fin 7 ⊕ Fin 7 ⊕ Fin 7 ⊕ Unit ⊕ Unit ⊕
  (Fin 63 × Fin 14) ⊕ Fin 21 ⊕ Fin 7 ⊕ Unit

/-- `Name` as a sum type. -/
def Name.toSum : Name → NameSum
  | src k => .inl k
  | ci k t => .inr (.inl (k, t))
  | ch k t => .inr (.inr (.inl (k, t)))
  | cv k t => .inr (.inr (.inr (.inl (k, t))))
  | gc j => .inr (.inr (.inr (.inr (.inl j))))
  | gh j => .inr (.inr (.inr (.inr (.inr (.inl j)))))
  | gv j => .inr (.inr (.inr (.inr (.inr (.inr (.inl j))))))
  | ec l => .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl l)))))))
  | eh l => .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl l))))))))
  | ev l => .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl l)))))))))
  | rc => .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl ()))))))))))
  | rh => .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl ())))))))))))
  | tc k t =>
    .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (k, t)))))))))))))
  | tg j =>
    .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl j)))))))))))))
  | te l =>
    .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl l))))))))))))))
  | tr =>
    .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr ()))))))))))))))

def Name.ofSum : NameSum → Name
  | .inl k => src k
  | .inr (.inl (k, t)) => ci k t
  | .inr (.inr (.inl (k, t))) => ch k t
  | .inr (.inr (.inr (.inl (k, t)))) => cv k t
  | .inr (.inr (.inr (.inr (.inl j)))) => gc j
  | .inr (.inr (.inr (.inr (.inr (.inl j))))) => gh j
  | .inr (.inr (.inr (.inr (.inr (.inr (.inl j)))))) => gv j
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl l))))))) => ec l
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl l)))))))) => eh l
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl l))))))))) => ev l
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl ())))))))))) => rc
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl ()))))))))))) => rh
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (k, t))))))))))))) =>
    tc k t
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl j))))))))))))) =>
    tg j
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl l)))))))))))))) =>
    te l
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr ())))))))))))))) =>
    tr

/-- `Name` is a sum type. -/
def Name.sumEquiv : Name ≃ NameSum where
  toFun := Name.toSum
  invFun := Name.ofSum
  left_inv n := by cases n <;> rfl
  right_inv s := by
    rcases s with k | ⟨k, t⟩ | ⟨k, t⟩ | ⟨k, t⟩ | j | j | j | l | l | l | ⟨⟩ | ⟨⟩ | ⟨k, t⟩ | j | l |
      ⟨⟩ <;> rfl

instance : Fintype Name := Fintype.ofEquiv NameSum Name.sumEquiv.symm

/-- Sums over names split by constructor. -/
theorem Name.sum_eq {M : Type} [AddCommMonoid M] (f : Name → M) :
    ∑ n, f n = (∑ k, f (src k)) + (∑ k, ∑ t, f (ci k t)) + (∑ k, ∑ t, f (ch k t)) +
      (∑ k, ∑ t, f (cv k t)) +
      (∑ j, f (gc j)) + (∑ j, f (gh j)) + (∑ j, f (gv j)) +
      (∑ l, f (ec l)) + (∑ l, f (eh l)) + (∑ l, f (ev l)) + f rc + f rh +
      (∑ k, ∑ t, f (tc k t)) + (∑ j, f (tg j)) + (∑ l, f (te l)) + f tr := by
  rw [← Fintype.sum_equiv Name.sumEquiv.symm (fun s => f (Name.ofSum s)) f (fun _ => rfl)]
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_unique, Name.ofSum,
    add_assoc]

/-! ## Tweaks

The random oracle has no labels: a hash node queries it on its parent's value alone.  The scheme
keeps its hash nodes apart by starting every hash input with a 128-bit tweak word naming the hash
node.  Convention: the tweak occupies the HIGH bits, i.e. the input of the hash node `h` is
`tw h ++ payload` (`BitVec.append`, whose left argument is the most significant one).  The
payload is recovered by `setWidth`/`extractLsb' 0`, the tweak by `extractLsb' n 128` or
`tagNat`. -/

/-- The tweak of the hash node `h`: its topological index, as a 128-bit word. -/
def tw (h : Name) : BitVec 128 := BitVec.ofNat 128 h.idx

theorem tw_toNat (h : Name) : (tw h).toNat = h.idx := by
  have := h.idx_lt
  unfold N at this
  rw [tw, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (by omega)

theorem tw_injective : Function.Injective tw := by
  intro h h' e
  apply Name.idx_injective
  rw [← tw_toNat h, ← tw_toNat h', e]

/-- A hash input determines its tweak and its payload. -/
theorem append_inj {n : ℕ} {a a' : BitVec 128} {u u' : BitVec n} (e : a ++ u = a' ++ u') :
    a = a' ∧ u = u' := by
  constructor
  · have := congrArg (fun z => z.extractLsb' n 128) e
    simpa only [BitVec.extractLsb'_append_eq_left] using this
  · have := congrArg (fun z => z.extractLsb' 0 n) e
    simpa only [BitVec.extractLsb'_append_eq_right] using this

/-- Equal hash inputs (of one length) belong to the same hash node and have the same payload. -/
theorem tw_append_inj {n : ℕ} {h h' : Name} {u u' : BitVec n} (e : tw h ++ u = tw h' ++ u') :
    h = h' ∧ u = u' :=
  ⟨tw_injective (append_inj e).1, (append_inj e).2⟩

/-- The number written in the 128 high bits of a query. -/
def tagNat (q : Query) : ℕ := q.2.toNat / 2 ^ (q.1 - 128)

theorem tagNat_append {n : ℕ} (a : BitVec 128) (u : BitVec n) :
    tagNat ⟨128 + n, a ++ u⟩ = a.toNat := by
  unfold tagNat
  simp only [BitVec.toNat_append, Nat.add_sub_cancel_left]
  rw [← Nat.shiftLeft_add_eq_or_of_lt u.isLt, Nat.shiftLeft_eq, Nat.add_comm,
    Nat.add_mul_div_right _ _ (Nat.two_pow_pos n), Nat.div_eq_of_lt u.isLt, Nat.zero_add]

/-- The tweak is read back from a hash input. -/
theorem tagNat_tw_append {n : ℕ} (h : Name) (u : BitVec n) :
    tagNat ⟨128 + n, tw h ++ u⟩ = h.idx := by
  rw [tagNat_append, tw_toNat]

/-- `tagNat` ignores casts. -/
theorem tagNat_cast {n m : ℕ} (e : n = m) (u : BitVec n) :
    tagNat ⟨m, u.cast e⟩ = tagNat ⟨n, u⟩ := by
  subst e; rfl

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

/-- The 128-bit truncation (the low half). -/
def trunc {w : ℕ} (x : BitVec w) : BitVec 128 := x.setWidth 128

/-- Assignments of the concrete graph. -/
abbrev Asg := (v : Fin N) → BitVec (lenF v)

/-- The deterministic value of a node, as a function of the assignment (only used for the
deterministic nodes; the function is defined on all names for convenience).  The hash inputs
`ci`, `gc`, `ec`, `rc` start with the tweak word of their hash node, read from its constant node,
in the high bits. -/
def detVal (n : Name) (x : Asg) : BitVec n.len :=
  match n with
  | .tc k t => tw (Name.ch k t)
  | .tg j => tw (Name.gh j)
  | .te l => tw (Name.eh l)
  | .tr => tw Name.rh
  | .ci k t => trunc (x (Name.tc k t).fin) ++ trunc (x (Name.prev k t).fin)
  | .cv k t => trunc (x (Name.ch k t).fin)
  | .gc j => trunc (x (Name.tg j).fin) ++ cat3 (trunc (x (Name.cv (Name.chainOf j 0) 13).fin))
      (trunc (x (Name.cv (Name.chainOf j 1) 13).fin)) (trunc (x (Name.cv (Name.chainOf j 2) 13).fin))
  | .gv j => trunc (x (Name.gh j).fin)
  | .ec l => trunc (x (Name.te l).fin) ++ cat3 (trunc (x (Name.gv (Name.groupOf l 0)).fin))
      (trunc (x (Name.gv (Name.groupOf l 1)).fin)) (trunc (x (Name.gv (Name.groupOf l 2)).fin))
  | .ev l => trunc (x (Name.eh l).fin)
  | .rc => trunc (x Name.tr.fin) ++ cat7 fun l => trunc (x (Name.ev l).fin)
  | _ => 0

/-- The value of the parent `p` of a hash node `h` carries the tweak of `h`, as soon as the
tweak word of `h` has its (constant) value. -/
theorem tagNat_detVal {p h : Name} (hc : Name.child p = some h) (hh : h.cost ≠ 0) (x : Asg)
    (hx : trunc (x (Name.twOf h).fin) = tw h) :
    tagNat ⟨p.len, detVal p x⟩ = h.idx := by
  cases p with
  | ci k t =>
    simp only [Name.child, Option.some.injEq] at hc; subst hc
    change trunc (x (Name.tc k t).fin) = _ at hx
    show tagNat ⟨128 + 128, trunc (x (Name.tc k t).fin) ++ _⟩ = _
    rw [hx]
    exact tagNat_tw_append _ _
  | gc j =>
    simp only [Name.child, Option.some.injEq] at hc; subst hc
    change trunc (x (Name.tg j).fin) = _ at hx
    show tagNat ⟨128 + 384, trunc (x (Name.tg j).fin) ++ _⟩ = _
    rw [hx]
    exact tagNat_tw_append _ _
  | ec l =>
    simp only [Name.child, Option.some.injEq] at hc; subst hc
    change trunc (x (Name.te l).fin) = _ at hx
    show tagNat ⟨128 + 384, trunc (x (Name.te l).fin) ++ _⟩ = _
    rw [hx]
    exact tagNat_tw_append _ _
  | rc =>
    simp only [Name.child, Option.some.injEq] at hc; subst hc
    change trunc (x Name.tr.fin) = _ at hx
    show tagNat ⟨128 + 896, trunc (x Name.tr.fin) ++ _⟩ = _
    rw [hx]
    exact tagNat_tw_append _ _
  | cv k t =>
    simp only [Name.child] at hc
    split_ifs at hc <;>
      (simp only [Option.some.injEq] at hc; subst hc; exact absurd rfl hh)
  | rh => simp only [Name.child, reduceCtorEq] at hc
  | src k => simp only [Name.child, Option.some.injEq] at hc; subst hc; exact absurd rfl hh
  | ch k t => simp only [Name.child, Option.some.injEq] at hc; subst hc; exact absurd rfl hh
  | gh j => simp only [Name.child, Option.some.injEq] at hc; subst hc; exact absurd rfl hh
  | gv j => simp only [Name.child, Option.some.injEq] at hc; subst hc; exact absurd rfl hh
  | eh l => simp only [Name.child, Option.some.injEq] at hc; subst hc; exact absurd rfl hh
  | ev l => simp only [Name.child, Option.some.injEq] at hc; subst hc; exact absurd rfl hh
  | tc k t => simp only [Name.child, Option.some.injEq] at hc; subst hc; exact absurd rfl hh
  | tg j => simp only [Name.child, Option.some.injEq] at hc; subst hc; exact absurd rfl hh
  | te l => simp only [Name.child, Option.some.injEq] at hc; subst hc; exact absurd rfl hh
  | tr => simp only [Name.child, Option.some.injEq] at hc; subst hc; exact absurd rfl hh

/-- The same, for the value as stored in the graph (cast to the length `graph.len p.fin`). -/
theorem tagNat_cast_detVal {p h : Name} (hc : Name.child p = some h) (hh : h.cost ≠ 0) (x : Asg)
    (hx : trunc (x (Name.twOf h).fin) = tw h)
    {m : ℕ} (e : p.len = m) : tagNat ⟨m, (detVal p x).cast e⟩ = h.idx := by
  rw [tagNat_cast, tagNat_detVal hc hh x hx]

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
  | ci k t =>
    show trunc (x (Name.tc k t).fin) ++ trunc (x (Name.prev k t).fin) =
      trunc (y (Name.tc k t).fin) ++ trunc (y (Name.prev k t).fin)
    rw [key (Name.prev k t) (by simp [Name.parents]), key (Name.tc k t) (by simp [Name.parents])]
  | cv k t =>
    show trunc (x (Name.ch k t).fin) = trunc (y (Name.ch k t).fin)
    rw [key (Name.ch k t) (by simp [Name.parents])]
  | gc j =>
    show trunc (x (Name.tg j).fin) ++ cat3 (trunc (x (Name.cv (Name.chainOf j 0) 13).fin))
        (trunc (x (Name.cv (Name.chainOf j 1) 13).fin))
        (trunc (x (Name.cv (Name.chainOf j 2) 13).fin)) =
      trunc (y (Name.tg j).fin) ++ cat3 (trunc (y (Name.cv (Name.chainOf j 0) 13).fin))
        (trunc (y (Name.cv (Name.chainOf j 1) 13).fin))
        (trunc (y (Name.cv (Name.chainOf j 2) 13).fin))
    rw [key (Name.tg j) (by simp [Name.parents]),
      key (Name.cv (Name.chainOf j 0) 13) (by simp [Name.parents]),
      key (Name.cv (Name.chainOf j 1) 13) (by simp [Name.parents]),
      key (Name.cv (Name.chainOf j 2) 13) (by simp [Name.parents])]
  | gv j =>
    show trunc (x (Name.gh j).fin) = trunc (y (Name.gh j).fin)
    rw [key (Name.gh j) (by simp [Name.parents])]
  | ec l =>
    show trunc (x (Name.te l).fin) ++ cat3 (trunc (x (Name.gv (Name.groupOf l 0)).fin))
        (trunc (x (Name.gv (Name.groupOf l 1)).fin))
        (trunc (x (Name.gv (Name.groupOf l 2)).fin)) =
      trunc (y (Name.te l).fin) ++ cat3 (trunc (y (Name.gv (Name.groupOf l 0)).fin))
        (trunc (y (Name.gv (Name.groupOf l 1)).fin))
        (trunc (y (Name.gv (Name.groupOf l 2)).fin))
    rw [key (Name.te l) (by simp [Name.parents]),
      key (Name.gv (Name.groupOf l 0)) (by simp [Name.parents]),
      key (Name.gv (Name.groupOf l 1)) (by simp [Name.parents]),
      key (Name.gv (Name.groupOf l 2)) (by simp [Name.parents])]
  | ev l =>
    show trunc (x (Name.eh l).fin) = trunc (y (Name.eh l).fin)
    rw [key (Name.eh l) (by simp [Name.parents])]
  | rc =>
    show trunc (x Name.tr.fin) ++ cat7 (fun l => trunc (x (Name.ev l).fin)) =
      trunc (y Name.tr.fin) ++ cat7 (fun l => trunc (y (Name.ev l).fin))
    have e : (fun l => trunc (x (Name.ev l).fin)) = fun l => trunc (y (Name.ev l).fin) := by
      funext l
      rw [key (Name.ev l) (Finset.mem_insert_of_mem
        (Finset.mem_image_of_mem _ (Finset.mem_univ _)))]
    rw [e, key Name.tr (Finset.mem_insert_self _ _)]
  | src _ => rfl
  | ch _ _ => rfl
  | gh _ => rfl
  | eh _ => rfl
  | rh => rfl
  | tc _ _ => rfl
  | tg _ => rfl
  | te _ => rfl
  | tr => rfl

/-- A deterministic node of the graph. -/
def detKind (v : Fin N) (n : Name) (h : ofFin v = n) : NodeKind 256 N lenF v :=
  .det ((Name.parents n).map nameEquiv.toEmbedding)
      (by exact det_parents_lt h)
      (fun x => (detVal n x).cast (by rw [lenF, h]))
      (by intro x y hxy; exact congrArg _ (detVal_local _ x y hxy))

/-- The kind of the node `v = n.fin`. -/
def kindOf (v : Fin N) : (n : Name) → ofFin v = n → NodeKind 256 N lenF v
  | .src _, _ => .source
  | .ch k t, h => .hash (Name.ci k t).fin
      (by exact hash_parent_lt h (Finset.mem_singleton_self _)) (by rw [lenF, h]; rfl)
  | .gh j, h => .hash (Name.gc j).fin
      (by exact hash_parent_lt h (Finset.mem_singleton_self _)) (by rw [lenF, h]; rfl)
  | .eh l, h => .hash (Name.ec l).fin
      (by exact hash_parent_lt h (Finset.mem_singleton_self _)) (by rw [lenF, h]; rfl)
  | .rh, h => .hash Name.rc.fin
      (by exact hash_parent_lt h (Finset.mem_singleton_self _)) (by rw [lenF, h]; rfl)
  | .ci k t, h => detKind v _ h
  | .cv k t, h => detKind v _ h
  | .gc j, h => detKind v _ h
  | .gv j, h => detKind v _ h
  | .ec l, h => detKind v _ h
  | .ev l, h => detKind v _ h
  | .rc, h => detKind v _ h
  | .tc k t, h => detKind v _ h
  | .tg j, h => detKind v _ h
  | .te l, h => detKind v _ h
  | .tr, h => detKind v _ h

theorem kindOf_isHash (v : Fin N) (n : Name) (h : ofFin v = n) :
    (kindOf v n h).IsHash ↔ n.cost ≠ 0 := by
  cases n <;> simp [kindOf, detKind, NodeKind.IsHash, Name.cost]

theorem kindOf_isSource (v : Fin N) (n : Name) (h : ofFin v = n) :
    (kindOf v n h).IsSource ↔ ∃ k, n = .src k := by
  cases n <;> simp [kindOf, detKind, NodeKind.IsSource]

theorem kindOf_parents (v : Fin N) (n : Name) (h : ofFin v = n) :
    (kindOf v n h).parents = (Name.parents n).map nameEquiv.toEmbedding := by
  cases n <;> simp [kindOf, detKind, NodeKind.parents, Name.parents, nameEquiv]

/-- The computation graph of the scheme. -/
def graph : Graph paperParams where
  size := N
  len := lenF
  kind v := kindOf v (ofFin v) rfl
  root := Name.rh.fin
  root_isHash := (kindOf_isHash _ _ rfl).2 (by rw [ofFin_fin]; decide)

theorem graph_kind_eq (v : Fin N) (n : Name) (h : ofFin v = n) : graph.kind v = kindOf v n h := by
  subst h; rfl

theorem graph_kind_fin (n : Name) : graph.kind n.fin = kindOf n.fin n (ofFin_fin n) :=
  graph_kind_eq _ _ _

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
  cases n <;> simp only [kindOf, detKind, graph_len_fin] <;>
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
