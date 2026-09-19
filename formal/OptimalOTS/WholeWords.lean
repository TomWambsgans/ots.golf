import OptimalOTS.Statement

/-!
# Whole-word DAG schemes

Sources are independent 128-bit words. Each oracle output is 256 bits. A deterministic
node may select a fixed low or high 128-bit half directly from a hash node, or concatenate
any list of earlier values. Concatenation may repeat, reorder or group values, including
the empty list. Every value therefore consists of whole 128-bit words. There are no
nonempty constant nodes or other deterministic operations. Disclosure reveals a node's
complete value.

The underlying DAG cuts, nonce/index algorithms, oracle, costs, size limits and security
experiment are unchanged. In particular inputs have no fixed arity, and longer inputs
pay their full compression cost. This is a syntactic restriction, not a provenance budget.
-/

namespace OptimalOTS

/-- Sources have 128 bits, hashes have 256 bits, and deterministic nodes concatenate values
or select a fixed half directly from a hash node. -/
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

/-- A lower bound for every secure whole-word DAG scheme. -/
def WholeWordVerificationLowerBound (P : Params) (c : ℕ) : Prop :=
  ∀ S : Scheme P, S.graph.WholeWords → S.Secure → ∃ i, c ≤ S.verifyCost i

end OptimalOTS
