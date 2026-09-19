import Submissions.RiscvUpper.Refines
import Submissions.RiscvUpper.ForestVerifierProof

/-!
# Node sweeps with cycle accounting

A segment of the specification's node order is implemented by one machine region per node.
`Segment.NodeRefines` is the continuation-passing obligation for one node; `sweep_refines`
composes a whole segment, threading an invariant indexed by the segment's remaining nodes.
-/

namespace OptimalOTS.RiscvUpperProgram.Compact

open RiscvZkvm.Rv64 Forest Forest.Name RiscvUpperForest.ForestVerifier OracleComp

set_option allowUnsafeReducibility true
attribute [local reducible] Forest.graph
attribute [local irreducible] Forest.fixedPositions Forest.fixedDigits

variable (index : Idx paperParams) (payload : List Bool)

/-- The sequential reader, also returning its final cursor. -/
def runNodes' : List Name → graph.Assignment → ℕ →
    OracleComp (Spec paperParams) (graph.Assignment × ℕ)
  | [], x, cursor => pure (x, cursor)
  | n :: ns, x, cursor => cursorStep index payload x cursor n >>= fun r => runNodes' ns r.1 r.2

theorem runNodes_eq_fst (nodes : List Name) (x : graph.Assignment) (cursor : ℕ) :
    runNodes index payload nodes x cursor = Prod.fst <$> runNodes' index payload nodes x cursor := by
  induction nodes generalizing x cursor with
  | nil => simp [runNodes, runNodes']
  | cons n ns ih =>
    rw [runNodes, runNodes', map_bind]
    congr 1
    funext r
    rcases r with ⟨y, next⟩
    exact ih y next

theorem runNodes'_append (l₁ l₂ : List Name) (x : graph.Assignment) (cursor : ℕ) :
    runNodes' index payload (l₁ ++ l₂) x cursor =
      runNodes' index payload l₁ x cursor >>= fun r => runNodes' index payload l₂ r.1 r.2 := by
  induction l₁ generalizing x cursor with
  | nil => simp only [List.nil_append, runNodes', pure_bind]
  | cons n ns ih =>
    rw [List.cons_append, runNodes', runNodes', bind_assoc]
    simp only [ih]

/-- A machine implementation of one node kind: its code, charged cycles, and the invariant
holding between nodes, indexed by the remaining nodes of the segment. -/
structure Segment where
  code : Name → Code
  cost : Name → ℕ
  Inv : MachineState → graph.Assignment → ℕ → List Name → Prop

/-- The region for `n` refines `cursorStep` at `n`, re-establishes the invariant for the
remaining nodes, and lands on the following code, at the charged cost plus the continuation. -/
def Segment.NodeRefines (seg : Segment) (n : Name) : Prop :=
  ∀ (s : MachineState) (x : graph.Assignment) (cursor : ℕ) (rest : List Name) (tail : Code)
    (K : graph.Assignment × ℕ → OracleComp (Spec paperParams) (Option Bool)) (c budget fuel : ℕ),
    n ∉ rest → seg.Inv s x cursor (n :: rest) → Riscv.CodeAt s s.pc (seg.code n ++ tail) →
    (seg.code n).length + budget ≤ fuel →
    (∀ (t : MachineState) (r : graph.Assignment × ℕ),
      r ∈ support (cursorStep index payload x cursor n) →
      seg.Inv t r.1 r.2 rest → Riscv.CodeAt t t.pc tail →
      ∀ left, budget ≤ left → Riscv.Refines left t (K r) c) →
    Riscv.Refines fuel s (cursorStep index payload x cursor n >>= K) (seg.cost n + c)

/-- A whole segment refines the sequential reader over its nodes. -/
theorem sweep_refines (seg : Segment) (nodes : List Name) (nodup : nodes.Nodup)
    (each : ∀ n ∈ nodes, seg.NodeRefines index payload n) (tail : Code)
    (K : graph.Assignment × ℕ → OracleComp (Spec paperParams) (Option Bool)) (c rest' : ℕ)
    (continuation : ∀ (t : MachineState) (y : graph.Assignment) (cursor' : ℕ),
      seg.Inv t y cursor' [] → Riscv.CodeAt t t.pc tail →
      ∀ left, rest' ≤ left → Riscv.Refines left t (K (y, cursor')) c) :
    ∀ (s : MachineState) (x : graph.Assignment) (cursor fuel : ℕ),
      seg.Inv s x cursor nodes → Riscv.CodeAt s s.pc (nodes.flatMap seg.code ++ tail) →
      (nodes.flatMap seg.code).length + rest' ≤ fuel →
      Riscv.Refines fuel s (runNodes' index payload nodes x cursor >>= K)
        ((nodes.map seg.cost).sum + c) := by
  induction nodes with
  | nil =>
    intro s x cursor fuel inv located bound
    simp only [runNodes', pure_bind, List.map_nil, List.sum_nil, Nat.zero_add]
    simp only [List.flatMap_nil, List.nil_append, List.length_nil, Nat.zero_add] at located bound
    exact continuation s x cursor inv located fuel bound
  | cons n ns ih =>
    intro s x cursor fuel inv located bound
    rw [runNodes', bind_assoc, List.map_cons, List.sum_cons, Nat.add_assoc]
    rw [List.flatMap_cons, List.append_assoc] at located
    rw [List.flatMap_cons, List.length_append] at bound
    obtain ⟨fresh, nodup'⟩ := List.nodup_cons.mp nodup
    apply each n (by simp) s x cursor ns (ns.flatMap seg.code ++ tail) _ _
      ((ns.flatMap seg.code).length + rest') fuel fresh inv located (by omega)
    intro t r hr inv' located' left hleft
    exact ih nodup' (fun m hm => each m (by simp [hm])) t r.1 r.2 left inv' located' hleft

/-- A node without machine code: the specification step is pure and the state is unchanged. -/
theorem Segment.NodeRefines.ofPure (seg : Segment) (n : Name) (empty : seg.code n = [])
    (cost : seg.cost n = 0)
    (step : ∀ (s : MachineState) (x : graph.Assignment) (cursor : ℕ) (rest : List Name),
      n ∉ rest → seg.Inv s x cursor (n :: rest) → ∀ r ∈ support (cursorStep index payload x cursor n),
        seg.Inv s r.1 r.2 rest)
    (pureStep : ∀ (x : graph.Assignment) (cursor : ℕ), ∃ r,
      cursorStep index payload x cursor n = pure r) :
    seg.NodeRefines index payload n := by
  intro s x cursor rest tail K c budget fuel fresh inv located bound continuation
  obtain ⟨r, hr⟩ := pureStep x cursor
  rw [hr, pure_bind, cost, Nat.zero_add]
  rw [empty, List.nil_append] at located
  rw [empty, List.length_nil, Nat.zero_add] at bound
  have mem : r ∈ support (cursorStep index payload x cursor n) := by rw [hr]; simp
  exact continuation s r mem (step s x cursor rest fresh inv r mem) located fuel bound

end OptimalOTS.RiscvUpperProgram.Compact
