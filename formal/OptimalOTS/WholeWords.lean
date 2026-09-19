import OptimalOTS.Dag

/-!
# Whole-word DAG schemes

Sources are independent 128-bit words. Each oracle output is 256 bits. A deterministic
node may be a fixed public 128-bit word (no parents), select a fixed low or high 128-bit half
directly from a hash node, or concatenate any list of earlier values. Concatenation may repeat,
reorder or group values, including the empty list. Every value therefore consists of whole
128-bit words. There are no other deterministic operations. Disclosure reveals a node's
complete value.

Everything else (cuts, signing, verification, the oracle, costs, size limits and security) is
the DAG model of `Dag.lean`; in particular a hash input of any length pays its full
compression cost.
-/

namespace OptimalOTS

/-- Sources have 128 bits, hashes have 256 bits, and deterministic nodes are fixed 128-bit words,
concatenate values or select a fixed half directly from a hash node. A node without parents
is constant because its function depends only on its parents. -/
def Graph.WholeWords {P : Params} (G : Graph P) : Prop :=
  P.hashBits = 256 ∧ ∀ v, match G.kind v with
  | .source => G.len v = 128
  | .hash .. => True
  | .det ps _ f _ =>
      (ps = ∅ ∧ G.len v = 128) ∨
      (∃ ws : List (Fin G.size), ps = ws.toFinset ∧
        G.len v = (ws.map G.len).sum ∧
        ∀ x, f x = ofBits (G.len v) (ws.flatMap fun w => toBits (x w))) ∨
      (∃ p, ∃ high : Bool, (G.kind p).IsHash ∧ ps = {p} ∧ G.len v = 128 ∧
        ∀ x, f x = ofBits (G.len v) ((toBits (x p)).drop (if high then 128 else 0)))

/-- Every secure whole-word DAG scheme has a signature index whose verification costs at least
`c` compressions. -/
def WholeWordVerificationLowerBound (P : Params) (c : ℕ) : Prop :=
  ∀ S : Scheme P, S.graph.WholeWords → S.Secure → ∃ i, c ≤ S.verifyCost i

end OptimalOTS
