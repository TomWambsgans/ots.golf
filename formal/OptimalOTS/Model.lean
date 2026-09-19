import VCVio.OracleComp.QueryTracking.RandomOracle.Basic
import VCVio.OracleComp.QueryTracking.QueryBound.Basic
import VCVio.OracleComp.Constructions.SampleableType
import VCVio.OracleComp.SimSemantics.Append
import VCVio.OracleComp.ProbComp
import VCVio.EvalDist.BitVec

/-!
# The shared model

The competition's parameters and budgets, the random oracle, and the cost of a query. Every
model (`Dag.lean`, `OracleAlgorithm.lean`, `RiscvMachine.lean`) builds on this file. All parties
share one random oracle on bit strings, without implicit labels or domain separation. Uniform
sampling is free; every hash query is charged for its complete input, including repeated queries.
-/

open OracleSpec OracleComp ENNReal

noncomputable section

open scoped Classical

namespace OptimalOTS

/-! ## 1. Parameters -/

/-- Lengths (in bits), the security level, and the budgets every scheme must respect. -/
structure Params where
  /-- Output length of the random oracle. -/
  hashBits : ℕ
  /-- Input bits per compression block. For positive `blockBits`, hashing `k` bits costs
  `max 1 ⌈k / blockBits⌉`. -/
  blockBits : ℕ
  /-- Public-key length. -/
  pkBits : ℕ
  /-- Length of messages. -/
  msgBits : ℕ
  /-- Security level; see the `Secure` definitions of the models. -/
  securityBits : ℕ
  /-- Maximal signature length in bits, including any nonce. -/
  signatureBits : ℕ
  /-- Maximal query cost of key generation, in compressions. -/
  keygenCost : ℕ
  /-- Maximal query cost of signing, in compressions. -/
  signCost : ℕ

/-- The competition's parameters. -/
def paperParams : Params where
  hashBits := 256
  blockBits := 512
  pkBits := 128
  msgBits := 256
  securityBits := 127
  signatureBits := 5376
  keygenCost := 1024
  signCost := 2 ^ 20

abbrev Message (P : Params) := BitVec P.msgBits
abbrev PublicKey (P : Params) := BitVec P.pkBits

/-! ## 2. The random oracle and the cost of a query -/

/-- A bit string of any length, used as a random-oracle input. There are no implicit labels or
tweaks: equal strings share an answer. Explicit prefixes are part of the input and incur their
full query cost. -/
abbrev Query := Σ k : ℕ, BitVec k

/-- The random oracle: an independent uniform `hashBits`-bit answer for every query. -/
abbrev hashSpec (P : Params) : OracleSpec Query := Query →ₒ BitVec P.hashBits

/-- The oracles of every party: free uniform sampling and the random oracle. -/
abbrev Spec (P : Params) := unifSpec + hashSpec P

/-- Cost of hashing `k` bits: the number of started blocks, and at least one. -/
def blockCost (P : Params) (k : ℕ) : ℕ := max 1 ((k + P.blockBits - 1) / P.blockBits)

/-- Cost of a query: uniform sampling is free, hashing `k` bits costs `blockCost P k`. -/
def queryCost (P : Params) : (Spec P).Domain → ℕ
  | .inl _ => 0
  | .inr q => blockCost P q.1

/-- `oa` costs at most `B` on every execution path, whatever the oracle answers. -/
def CostAtMost (P : Params) {α : Type} (oa : OracleComp (Spec P) α) (B : ℕ) : Prop :=
  oa.IsQueryBound B (fun t b => queryCost P t ≤ b) (fun t b => b - queryCost P t)

/-- Query the random oracle on input `u`. -/
def hash (P : Params) {k : ℕ} (u : BitVec k) : OracleComp (Spec P) (BitVec P.hashBits) :=
  liftM ((Spec P).query (.inr ⟨k, u⟩))

/-- Sample a uniform bit string (free). -/
def sampleBits (P : Params) (n : ℕ) : OracleComp (Spec P) (BitVec n) :=
  liftM ($ᵗ BitVec n : ProbComp (BitVec n))

/-- Random-oracle semantics: uniform sampling is forwarded, and every hash query is answered by
one lazily sampled table shared by the whole experiment. -/
def oracleImpl (P : Params) : QueryImpl (Spec P) (StateT (hashSpec P).QueryCache ProbComp) :=
  (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget
      (StateT (hashSpec P).QueryCache ProbComp) +
    randomOracle (spec := hashSpec P)

/-- Probability that a Boolean experiment outputs `true` in the random-oracle model. -/
def probTrue (P : Params) (oa : OracleComp (Spec P) Bool) : ℝ≥0∞ :=
  Pr[= true | (simulateQ (oracleImpl P) oa).run' ∅]

/-! ## 3. Bit strings -/

/-- The bits of `x`, least significant first. -/
def toBits {n : ℕ} (x : BitVec n) : List Bool := List.ofFn fun i : Fin n => x.getLsbD i

/-- Interpret the list least significant bit first, truncating or zero-extending to `n` bits. -/
def ofBits (n : ℕ) (l : List Bool) : BitVec n :=
  BitVec.ofNat n (l.foldr (fun b acc => b.toNat + 2 * acc) 0)

end OptimalOTS
