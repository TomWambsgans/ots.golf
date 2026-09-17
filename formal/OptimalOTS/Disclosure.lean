import OptimalOTS.Statement

/-!
# Hash origins of disclosed values

Follow declared parent edges backwards, stopping at each hash node: these nodes are the
value's hash origins. Sources have none. Each hash is its own origin, regardless of its
inputs. Deterministic nodes inherit the union of their parents' origins, including parents
whose values their function ignores. Origins are graph nodes, not oracle inputs or labels.

This helper class bounds the union of origins across a disclosed payload. It supports the
whole-word lower proof and the legacy partial-disclosure certificates. `WholeWords` defines
the syntactic restriction for the third lower framework. Oracle semantics, costs and
security experiments are unchanged.
-/

noncomputable section
open scoped Classical

namespace OptimalOTS
namespace Graph

variable {P : Params} (G : Graph P)

/-- `HashOrigin h v` reaches hash node `h` from `v` without passing another hash. -/
inductive HashOrigin : Fin G.size → Fin G.size → Prop
  | hash {h} : (G.kind h).IsHash → HashOrigin h h
  | step {h v w} : ¬ (G.kind v).IsHash → w ∈ (G.kind v).parents →
      HashOrigin h w → HashOrigin h v

/-- The structurally defined hash origins of one node. -/
def hashOrigins (v : Fin G.size) : Finset (Fin G.size) :=
  Finset.univ.filter fun h => G.HashOrigin h v

/-- The union of a payload's hash origins, counting each node once. -/
def disclosureOrigins (A : Finset (Fin G.size)) : Finset (Fin G.size) :=
  A.biUnion G.hashOrigins

end Graph

/-- Every disclosure set has at most `b` distinct hash origins. -/
def Scheme.DisclosureBound {P : Params} (S : Scheme P) (b : ℕ) : Prop :=
  ∀ i, (S.graph.disclosureOrigins (S.sets i)).card ≤ b

/-- A lower bound for weakly secure DAG schemes with at most `b` disclosed hash origins. -/
def DisclosureVerificationLowerBound (P : Params) (b c : ℕ) : Prop :=
  ∀ S : Scheme P, S.DisclosureBound b → S.WeaklySecure → ∃ i, c ≤ S.verifyCost i

end OptimalOTS
