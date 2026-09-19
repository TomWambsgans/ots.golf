import Submissions.RiscvUpper.Wire

/-!
# An explicit forest interpreter

The interpreter visits named nodes in topological order. Its equivalence to the certified
forest is equality of oracle computations, preserving queries and rejecting executions.
-/

open OracleComp
noncomputable section
open scoped Classical

namespace OptimalOTS.RiscvUpperForest.ForestVerifier

open Forest Forest.Name

set_option allowUnsafeReducibility true
attribute [local reducible] Forest.graph
set_option maxRecDepth 4000
attribute [local irreducible] Forest.setsName Forest.fixedChoice Forest.fixedPositions Forest.fixedDigits

/-- The nodes of chain `k`, in topological order. -/
def chainNodes (k : Fin 63) : List Name :=
  src k :: (List.finRange 14).flatMap (fun t => [ci k t, ch k t, cv k t])

/-- Topological order: the chains one after the other, then the tree. -/
def order : List Name :=
  (List.finRange 63).flatMap chainNodes ++
  (List.finRange 21).map gc ++ (List.finRange 21).map gh ++
  (List.finRange 21).map gv ++ (List.finRange 7).map ec ++
  (List.finRange 7).map eh ++ (List.finRange 7).map ev ++ [rc, rh]

set_option maxRecDepth 100000 in
theorem order_fin : order.map Name.fin = List.finRange N := by decide +kernel

/-- The operation attached to a named node. -/
def evalName (x : graph.Assignment) (n : Name) :
    OracleComp (Spec paperParams) (BitVec (graph.len n.fin)) :=
  match n with
  | .src _ => pure 0
  | .ch k t => (fun y => y.cast (graph_len_fin (.ch k t)).symm) <$>
      hash paperParams (x (ci k t).fin)
  | .gh j => (fun y => y.cast (graph_len_fin (.gh j)).symm) <$>
      hash paperParams (x (gc j).fin)
  | .eh l => (fun y => y.cast (graph_len_fin (.eh l)).symm) <$>
      hash paperParams (x (ec l).fin)
  | .rh => (fun y => y.cast (graph_len_fin .rh).symm) <$>
      hash paperParams (x rc.fin)
  | .ci k t => pure ((detVal (.ci k t) x).cast (graph_len_fin (.ci k t)).symm)
  | .cv k t => pure ((detVal (.cv k t) x).cast (graph_len_fin (.cv k t)).symm)
  | .gc j => pure ((detVal (.gc j) x).cast (graph_len_fin (.gc j)).symm)
  | .gv j => pure ((detVal (.gv j) x).cast (graph_len_fin (.gv j)).symm)
  | .ec l => pure ((detVal (.ec l) x).cast (graph_len_fin (.ec l)).symm)
  | .ev l => pure ((detVal (.ev l) x).cast (graph_len_fin (.ev l)).symm)
  | .rc => pure ((detVal .rc x).cast (graph_len_fin .rc).symm)

theorem evalName_eq (x : graph.Assignment) (n : Name) :
    evalName x n = graph.evalNode x n.fin (pure 0) := by
  unfold Graph.evalNode
  rw [graph_kind_fin]
  cases n <;> rfl

/-- A finite test for a node being reachable from the root. -/
def reachable (A : Finset Name) (n : Name) : Bool :=
  (ancSet n).toList.all fun a => decide (a ∉ A)

theorem reachable_eq_true (A : Finset Name) (n : Name) :
    reachable A n = true ↔ graph.Visited (fins A) n.fin := by
  rw [visited_iff]
  simp only [reachable, List.all_eq_true, Finset.mem_toList, decide_eq_true_eq,
    above_iff_mem_ancSet]

/-- Read a disclosed value, compute a visited node, or assign zero. -/
def step (A : Finset Name) (given x : graph.Assignment) (n : Name) :
    OracleComp (Spec paperParams) graph.Assignment :=
  if n ∈ A then pure (Function.update x n.fin (given n.fin))
  else if reachable A n then Function.update x n.fin <$> evalName x n
  else pure (Function.update x n.fin 0)

theorem step_eq (A : Finset Name) (given x : graph.Assignment) (n : Name) :
    step A given x n = graph.reconStep (fins A) given x n.fin := by
  unfold step Graph.reconStep
  simp only [mem_fins, reachable_eq_true, evalName_eq]

/-- Reconstruction by the explicit topological sequence. -/
def reconstruct (A : Finset Name) (payload : List Bool) :
    OracleComp (Spec paperParams) graph.Assignment :=
  order.foldlM (step A (graph.decode (fins A) payload)) (fun _ => 0)

theorem reconstruct_eq (A : Finset Name) (payload : List Bool) :
    reconstruct A payload = graph.reconstruct (fins A) (graph.decode (fins A) payload) := by
  unfold reconstruct
  rw [Graph.reconstruct_eq_foldlM]
  change _ = (List.finRange N).foldlM _ _
  rw [← order_fin, List.foldlM_map]
  congr 1
  funext x n
  exact step_eq A _ x n

/-- Raw signatures begin with the 128-bit signing nonce. -/
def verify (pk : PublicKey paperParams) (m : Message paperParams) (bits : List Bool) :
    OracleComp (Spec paperParams) Bool := do
  let i ← index paperParams m (ofBits 128 (bits.take 128))
  if hi : i ∈ validSet paperParams then
    let A := Forest.setsName ⟨i, hi⟩
    if (bits.drop 128).length = graph.revealBits (fins A) then
      let y ← reconstruct A (bits.drop 128)
      return decide ((y rh.fin).setWidth 128 = pk)
    else return false
  else return false

/-- Exact equality to the verifier covered by the forest security certificate. -/
theorem verify_eq (pk : PublicKey paperParams) (m : Message paperParams) (bits : List Bool) :
    verify pk m bits = Wire.scheme.verify pk m bits := by
  change verify pk m bits = Forest.forestScheme.verify pk m (Wire.decode bits)
  unfold verify GScheme.verify Wire.decode
  apply congrArg (fun f => index paperParams m (ofBits 128 (bits.take 128)) >>= f)
  funext i
  by_cases hi : i ∈ validSet paperParams
  · rw [dif_pos hi, dif_pos hi]
    change (if (bits.drop 128).length = graph.revealBits (fins (setsName ⟨i, hi⟩)) then _ else _) =
      (if (bits.drop 128).length = graph.revealBits (fins (setsName ⟨i, hi⟩)) then _ else _)
    split_ifs with hlen
    · rw [reconstruct_eq]
      congr 1
      funext y
      exact congrArg pure (by congr)
    · rfl
  · rw [dif_neg hi, dif_neg hi]

/-- The finite operation vocabulary compiled to RV64IM. -/
inductive NodeOp where
  | zero
  | copy (source : Name)
  | tagged1 (tag : BitVec 16) (source : Name)
  | tagged3 (tag : BitVec 16) (a b c : Name)
  | tagged7 (tag : BitVec 16) (children : Fin 7 → Name)
  | hash (source : Name)

/-- The static operation at each named node. -/
def nodeOp : Name → NodeOp
  | .src _ => .zero
  | .ci k t => .tagged1 (tw (ch k t)) (prev k t)
  | .ch k t => .hash (ci k t)
  | .cv k t => .copy (ch k t)
  | .gc j => .tagged3 (tw (gh j)) (cv (chainOf j 0) 13)
      (cv (chainOf j 1) 13) (cv (chainOf j 2) 13)
  | .gh j => .hash (gc j)
  | .gv j => .copy (gh j)
  | .ec l => .tagged3 (tw (eh l)) (gv (groupOf l 0))
      (gv (groupOf l 1)) (gv (groupOf l 2))
  | .eh l => .hash (ec l)
  | .ev l => .copy (eh l)
  | .rc => .tagged7 (tw rh) ev
  | .rh => .hash rc

/-- Numerical value produced by an operation, before storage in the destination slot. -/
def evalOp (x : graph.Assignment) : NodeOp → OracleComp (Spec paperParams) ℕ
  | .zero => pure 0
  | .copy source => pure (trunc (x source.fin)).toNat
  | .tagged1 tag source => pure (tag ++ trunc (x source.fin)).toNat
  | .tagged3 tag a b c =>
      pure (tag ++ cat3 (trunc (x a.fin)) (trunc (x b.fin)) (trunc (x c.fin))).toNat
  | .tagged7 tag children => pure (tag ++ cat7 fun l => trunc (x (children l).fin)).toNat
  | .hash source => BitVec.toNat <$> OptimalOTS.hash paperParams (x source.fin)

/-- Write an operation's output using the destination node's specified length. -/
def runOp (x : graph.Assignment) (n : Name) :
    OracleComp (Spec paperParams) (BitVec (graph.len n.fin)) :=
  (fun y => y.cast (graph_len_fin n).symm) <$>
    (BitVec.ofNat n.len <$> evalOp x (nodeOp n))

private theorem cast_zero {n m : ℕ} (h : n = m) : (0 : BitVec n).cast h = 0 := by
  subst h
  rfl

/-- Every operation preserves the graph's exact bit order and hash input length. -/
theorem runOp_eq (x : graph.Assignment) (n : Name) : runOp x n = evalName x n := by
  cases n <;> dsimp only [runOp, nodeOp, evalOp, evalName, detVal, Name.len]
  all_goals simp only [map_pure, Functor.map_map,
    BitVec.ofNat_toNat, BitVec.setWidth_eq]
  all_goals first
    | exact congrArg pure (cast_zero _)
    | (apply congrArg (fun f => f <$> _); funext y;
       exact congrArg (fun z => z.cast _) (BitVec.setWidth_eq y))

/-- Whether a node supplies one of the 41 signature words. -/
def disclosed (positions : Fin 63 → Fin 15) : Name → Bool
  | .src k => decide (k.val < 36 ∧ (positions k).val = 0)
  | .cv k t => decide (k.val < 36 ∧ (positions k).val = t.val + 1)
  | .gv j => decide (12 ≤ j.val ∧ j.val < 15)
  | .ev l => decide (5 ≤ l.val)
  | _ => false

/-- Whether a node is computed from earlier nodes rather than read from the signature. -/
def evaluated (positions : Fin 63 → Fin 15) : Name → Bool
  | .src _ => false
  | .ci k t | .ch k t | .cv k t => decide (k.val < 36 ∧ (positions k).val ≤ t.val)
  | .gc j | .gh j | .gv j => decide (j.val < 12)
  | .ec l | .eh l | .ev l => decide (l.val < 5)
  | .rc | .rh => true

/-- The machine's disclosure predicate agrees with the certified cut. -/
theorem disclosed_eq (i : Idx paperParams) (n : Name) :
    disclosed (fixedPositions i) n = true ↔ n ∈ Forest.setsName i := by
  rw [Forest.setsName]
  cases n with
  | src k =>
    rw [src_mem_cutOf_iff']
    simp only [disclosed, decide_eq_true_eq, fixedChoice, fixed_active, Fin.ext_iff, Fin.val_zero]
  | cv k t =>
    rw [cv_mem_cutOf_iff']
    simp only [disclosed, decide_eq_true_eq, fixedChoice, fixed_active]
  | gv j =>
    rw [gv_mem_cutOf_iff']
    simp only [disclosed, decide_eq_true_eq, fixedChoice, fixedG, Finset.mem_insert,
      Finset.mem_singleton, Fin.ext_iff]
    omega
  | ev l =>
    rw [ev_mem_cutOf_iff']
    simp only [disclosed, decide_eq_true_eq, fixedChoice, fixedE, Finset.mem_insert,
      Finset.mem_singleton, Fin.ext_iff]
    omega
  | ci k t => simp only [disclosed, Bool.false_eq_true, ci_not_mem_cutOf]
  | ch k t => simp only [disclosed, Bool.false_eq_true, ch_not_mem_cutOf]
  | gc j => simp only [disclosed, Bool.false_eq_true, gc_not_mem_cutOf]
  | gh j => simp only [disclosed, Bool.false_eq_true, gh_not_mem_cutOf]
  | ec l => simp only [disclosed, Bool.false_eq_true, ec_not_mem_cutOf]
  | eh l => simp only [disclosed, Bool.false_eq_true, eh_not_mem_cutOf]
  | rc => simp only [disclosed, Bool.false_eq_true, rc_not_mem_cutOf]
  | rh => simp only [disclosed, Bool.false_eq_true, rh_not_mem_cutOf]

private theorem evaluated_child {A : Finset Name} {n p : Name} (hc : child n = some p)
    (he : Evaluated A n) : Evaluated A p :=
  ⟨he.2 p (Above.child hc), fun m hm => he.2 m (Above.step hc hm)⟩

/-- The machine's computation predicate agrees with the certified reconstruction. -/
theorem evaluated_eq (i : Idx paperParams) (n : Name) :
    evaluated (fixedPositions i) n = true ↔ Evaluated (Forest.setsName i) n := by
  rw [Forest.setsName]
  have chain (k : Fin 63) (t : Fin 14) :
      Evaluated (cutOf (fixedChoice i)) (ch k t) ↔
        k.val < 36 ∧ (fixedPositions i k).val ≤ t.val := by
    rw [evaluated_ch_iff']
    simp only [fixedChoice, fixed_active]
  have group (j : Fin 21) :
      Evaluated (cutOf (fixedChoice i)) (gh j) ↔ j.val < 12 := by
    rw [evaluated_gh_iff']
    simp only [fixedChoice, fixedE, fixedG, subtreeOf, Finset.mem_insert,
      Finset.mem_singleton, Fin.ext_iff]
    omega
  have subtree (l : Fin 7) :
      Evaluated (cutOf (fixedChoice i)) (eh l) ↔ l.val < 5 := by
    rw [evaluated_eh_iff']
    simp only [fixedChoice, fixedE, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
    omega
  cases n with
  | src k =>
    simp only [evaluated, Bool.false_eq_true, false_iff]
    intro h
    rcases (fixedCut_isCut i).covers k with hk | ⟨m, hm, ha⟩
    · exact h.1 hk
    · exact h.2 m ha hm
  | ci k t =>
    rw [evaluated_ci_iff']
    simp only [evaluated, decide_eq_true_eq, fixedChoice, fixed_active]
  | ch k t => exact by simpa only [evaluated, decide_eq_true_eq] using (chain k t).symm
  | cv k t =>
    simp only [evaluated, decide_eq_true_eq]
    rw [← chain k t]
    exact ⟨evaluated_child rfl, evaluated_of_child rfl (ch_not_mem_cutOf _ _ _)⟩
  | gc j =>
    simp only [evaluated, decide_eq_true_eq]
    rw [← group j]
    exact ⟨evaluated_of_child rfl (gc_not_mem_cutOf _ _), evaluated_child rfl⟩
  | gh j => simpa only [evaluated, decide_eq_true_eq] using (group j).symm
  | gv j =>
    simp only [evaluated, decide_eq_true_eq]
    rw [← group j]
    exact ⟨evaluated_child rfl, evaluated_of_child rfl (gh_not_mem_cutOf _ _)⟩
  | ec l =>
    simp only [evaluated, decide_eq_true_eq]
    rw [← subtree l]
    exact ⟨evaluated_of_child rfl (ec_not_mem_cutOf _ _), evaluated_child rfl⟩
  | eh l => simpa only [evaluated, decide_eq_true_eq] using (subtree l).symm
  | ev l =>
    simp only [evaluated, decide_eq_true_eq]
    rw [← subtree l]
    exact ⟨evaluated_child rfl, evaluated_of_child rfl (eh_not_mem_cutOf _ _)⟩
  | rc => exact iff_of_true rfl (evaluated_rc' _)
  | rh => exact iff_of_true rfl (evaluated_rh' _)

end OptimalOTS.RiscvUpperForest.ForestVerifier
