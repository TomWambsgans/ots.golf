import OptimalOTS.Statement

/-!
# Whole-word DAG schemes

Sources are independent 128-bit words. Each oracle output is 256 bits; either fixed
128-bit half may be selected. The only other deterministic operation is concatenation.
Concatenations may repeat, reorder or group earlier values and may be empty. Thus every
value is a sequence of whole words. There are no nonempty constant nodes or other
deterministic transformations. A disclosed node reveals its complete value.

The underlying DAG cuts, nonce/index algorithms, oracle, costs, size limits and security
experiment are unchanged. In particular inputs have no fixed arity, and longer inputs
pay their full compression cost. This is a syntactic restriction, not a provenance budget.
-/

namespace OptimalOTS

/-- Every node uses only sources, hashing, concatenation, or a fixed half of a hash. -/
def Graph.WholeWords {P : Params} (G : Graph P) : Prop :=
  P.hashBits = 256 ∧ ∀ v, match G.kind v with
  | .source => G.len v = 128
  | .hash .. => True
  | .det ps _ f _ =>
      (∃ ws : List (Fin G.size), ps = ws.toFinset ∧
        G.len v = (ws.map G.len).sum ∧
        ∀ x, f x = ofBits (G.len v) (ws.flatMap fun w => toBits (x w))) ∨
      (∃ p, ∃ high : Bool, (G.kind p).IsHash ∧ ps = {p} ∧ G.len v = 128 ∧
        ∀ x, f x = ofBits (G.len v) ((toBits (x p)).drop (if high then 128 else 0)))

/-- The third lower framework: a DAG whose operations preserve whole 128-bit words. -/
def Scheme.WholeWords {P : Params} (S : Scheme P) : Prop := S.graph.WholeWords

/-- A lower bound for every weakly secure whole-word DAG scheme. -/
def WholeWordVerificationLowerBound (P : Params) (c : ℕ) : Prop :=
  ∀ S : Scheme P, S.WholeWords → S.WeaklySecure → ∃ i, c ≤ S.verifyCost i

end OptimalOTS
