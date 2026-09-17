import OptimalOTS.Statement

/-!
# Partial disclosures from a bounded number of hash outputs

An origin is the first hash node reached by walking backwards through deterministic nodes.
Sources have no hash origins. Hashing starts a new origin, even when its input depends on many
earlier hashes. Deterministic processing, including slicing and error-correcting encoding,
inherits the union of its parents' origins. Origins are graph nodes, not oracle labels.

The restriction concerns the union for the whole disclosed payload. All bit lengths, query
costs, the bare oracle, and the DAG reconstruction and security experiments remain unchanged.
-/

noncomputable section
open scoped Classical

namespace OptimalOTS
namespace Graph

variable {P : Params} (G : Graph P)

/-- Hash provenance through any number of deterministic operations. -/
inductive HashOrigin : Fin G.size → Fin G.size → Prop
  | hash {h} : (G.kind h).IsHash → HashOrigin h h
  | step {h v w} : ¬ (G.kind v).IsHash → w ∈ (G.kind v).parents →
      HashOrigin h w → HashOrigin h v

/-- Distinct underlying hash nodes of one value; secret sources contribute none. -/
def hashOrigins (v : Fin G.size) : Finset (Fin G.size) :=
  Finset.univ.filter fun h => G.HashOrigin h v

/-- Hash outputs represented in a disclosed payload, counting shared origins once. -/
def disclosureOrigins (A : Finset (Fin G.size)) : Finset (Fin G.size) :=
  A.biUnion G.hashOrigins

end Graph

/-- Partial disclosures may represent at most `b` distinct hash outputs per signature. -/
def Scheme.DisclosureBound {P : Params} (S : Scheme P) (b : ℕ) : Prop :=
  ∀ i, (S.graph.disclosureOrigins (S.sets i)).card ≤ b

/-- The third framework retains the complete bare-oracle DAG security experiment. -/
def DisclosureVerificationLowerBound (P : Params) (b c : ℕ) : Prop :=
  ∀ S : Scheme P, S.DisclosureBound b → S.WeaklySecure → ∃ i, c ≤ S.verifyCost i

end OptimalOTS
