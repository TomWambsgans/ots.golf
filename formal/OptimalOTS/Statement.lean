import VCVio.OracleComp.QueryTracking.RandomOracle.Basic
import VCVio.OracleComp.QueryTracking.QueryBound.Basic
import VCVio.OracleComp.Constructions.SampleableType
import VCVio.OracleComp.SimSemantics.Append
import VCVio.OracleComp.ProbComp
import VCVio.EvalDist.BitVec

/-!
# Verification cost of hash-based one-time signatures: the statement

This file is the contract of both tracks; nothing here is proof-related.

```
upper track:  S : Scheme paperParams,   S.Secure,   ∀ i, S.verifyCost i ≤ c
lower track:  VerificationLowerBound paperParams c :=
                ∀ S : Scheme paperParams, S.WeaklySecure → ∃ i, c ≤ S.verifyCost i
```

In words: with the parameters of the paper (a 128-bit public key, at most 5248 revealed bits per
signature, 127 bits of security), an upper-track certificate is a graph-based one-time signature
scheme, strongly unforgeable, all of whose signatures verify within `c` compressions; a lower-track
certificate shows that every such scheme, even one that is only existentially unforgeable, has a
signature whose verification costs at least `c` compressions. Strong security implies weak
security (every win of `weakExperiment` is a win of `experiment`, at the same cost; proved in
`OptimalOTS/Weak.lean`), so the two tracks bound the same number from both sides.

The file is organized as follows.

1. `Params`: the numerical parameters.
2. The random oracle and the cost of a query (one compression per started 512-bit block).
3. Computation graphs: secret sources, deterministic nodes and hash nodes.
4. Schemes: disclosure sets, key generation, signing, verification, and the verification cost.
5. Security: the one-signature forgery experiment and `Scheme.Secure`.
6. The lower-bound statement and the parameters of the paper.
-/

open OracleSpec OracleComp ENNReal

noncomputable section

open scoped Classical

namespace OptimalOTS

/-! ## 1. Parameters -/

/-- The numerical parameters. -/
structure Params where
  /-- Output length of the random oracle. -/
  hashBits : ℕ
  /-- A query on `k` input bits costs `⌈k / blockBits⌉` compressions (and at least one). Nothing
  else is charged: a per-key public parameter can be absorbed once, in a block of its own, and the
  chaining state reused by every later query (an observation of Justin Drake). -/
  blockBits : ℕ
  /-- Length of the public key: a prefix of the root hash. -/
  pkBits : ℕ
  /-- Length of messages. -/
  msgBits : ℕ
  /-- Length of signing nonces. -/
  nonceBits : ℕ
  /-- Number of bits of `H(m ‖ η)` read as the disclosure index. -/
  idxBits : ℕ
  /-- Maximal number of revealed bits in a signature, excluding the nonce. -/
  maxRevealBits : ℕ
  /-- Maximal query cost of key generation. -/
  keygenBudget : ℕ
  /-- Number of disclosure sets. -/
  numSets : ℕ
  /-- Maximal number of nonces tried by the signer. -/
  trialLimit : ℕ
  /-- Forging with total cost `B` must succeed with probability `< B / 2 ^ securityBits`. -/
  securityBits : ℕ

/-! ## 2. The random oracle and the cost of a query -/

/-- A random-oracle query: a bit string of any length. There is one oracle and nothing else: no
labels, no tweaks, no domain separation. A scheme that wants its queries kept apart, from one another
or from the index query, arranges it in the strings it hashes and pays for their bits. -/
abbrev Query := Σ k : ℕ, BitVec k

/-- The random oracle: an independent uniform `hashBits`-bit answer for every query. -/
abbrev hashSpec (P : Params) : OracleSpec Query := Query →ₒ BitVec P.hashBits

/-- The oracles of every party: free uniform sampling and the random oracle. -/
abbrev Spec (P : Params) := unifSpec + hashSpec P

/-- Cost of hashing `k` bits: the number of started blocks, and at least one. -/
def blockCost (P : Params) (k : ℕ) : ℕ := max 1 ((k + P.blockBits - 1) / P.blockBits)

/-- Cost of the index query `H(m ‖ η)`. -/
def idxCost (P : Params) : ℕ := blockCost P (P.msgBits + P.nonceBits)

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

/-! ## 3. Computation graphs -/

/-- The kind of node `v` in a graph with `N` nodes and output lengths `len`. Parents precede their
children, so the order of `Fin N` is a topological order. -/
inductive NodeKind (hashBits N : ℕ) (len : Fin N → ℕ) (v : Fin N) : Type where
  /-- A secret source: a uniformly random string. -/
  | source
  /-- A deterministic node: any public function of its parents' values. The function receives
  all node values but may only depend on those of its parents. -/
  | det (parents : Finset (Fin N)) (parents_lt : ∀ w ∈ parents, w < v)
      (f : ((w : Fin N) → BitVec (len w)) → BitVec (len v))
      (f_local : ∀ x y : (w : Fin N) → BitVec (len w),
        (∀ w ∈ parents, x w = y w) → f x = f y)
  /-- A hash node: the random oracle on its parent's value. -/
  | hash (parent : Fin N) (parent_lt : parent < v) (len_eq : len v = hashBits)

namespace NodeKind

variable {hashBits N : ℕ} {len : Fin N → ℕ} {v : Fin N}

/-- The parents of a node. -/
def parents : NodeKind hashBits N len v → Finset (Fin N)
  | source => ∅
  | det ps _ _ _ => ps
  | hash p _ _ => {p}

/-- The node is a secret source. -/
def IsSource : NodeKind hashBits N len v → Prop
  | source => True
  | _ => False

/-- The node is a hash node. -/
def IsHash : NodeKind hashBits N len v → Prop
  | hash .. => True
  | _ => False

end NodeKind

/-- A public computation graph. -/
structure Graph (P : Params) where
  /-- Number of nodes. -/
  size : ℕ
  /-- Output length of each node. -/
  len : Fin size → ℕ
  /-- The kind of each node. -/
  kind : (v : Fin size) → NodeKind P.hashBits size len v
  /-- The root; a prefix of its value is the public key. -/
  root : Fin size
  root_isHash : (kind root).IsHash

/-- The bits of `x`, least significant first. -/
def toBits {n : ℕ} (x : BitVec n) : List Bool := List.ofFn fun i : Fin n => x.getLsbD i

/-- Read `n` bits, least significant first. -/
def ofBits (n : ℕ) (l : List Bool) : BitVec n :=
  BitVec.ofNat n (l.foldr (fun b acc => b.toNat + 2 * acc) 0)

namespace Graph

variable {P : Params} (G : Graph P)

/-- A value for every node. -/
abbrev Assignment := (v : Fin G.size) → BitVec (G.len v)

/-- Query cost of evaluating node `v`: the block cost of its input for a hash node, else zero. -/
def nodeCost (v : Fin G.size) : ℕ :=
  match G.kind v with
  | .hash p _ _ => blockCost P (G.len p)
  | _ => 0

/-- Query cost of key generation, which evaluates every node once. -/
def keygenCost : ℕ := ∑ v, G.nodeCost v

/-- The nodes reached by walking backwards from the root, stopping at the nodes of `A`. -/
inductive Visited (A : Finset (Fin G.size)) : Fin G.size → Prop
  | root : Visited A G.root
  | parent {w v : Fin G.size} : Visited A w → w ∉ A → v ∈ (G.kind w).parents → Visited A v

/-- The nodes evaluated when reconstructing the root from the values on `A`. -/
def evaluated (A : Finset (Fin G.size)) : Finset (Fin G.size) :=
  Finset.univ.filter fun v => G.Visited A v ∧ v ∉ A

/-- Query cost of reconstructing the root from the values on `A`. -/
def reconstructCost (A : Finset (Fin G.size)) : ℕ := ∑ v ∈ G.evaluated A, G.nodeCost v

/-- Number of bits of the values on `A`. -/
def revealBits (A : Finset (Fin G.size)) : ℕ := ∑ v ∈ A, G.len v

/-- Compute node `v` from the values `x` of earlier nodes; `onSource` gives a source's value. -/
def evalNode (x : G.Assignment) (v : Fin G.size)
    (onSource : OracleComp (Spec P) (BitVec (G.len v))) :
    OracleComp (Spec P) (BitVec (G.len v)) :=
  match G.kind v with
  | .source => onSource
  | .det _ _ f _ => pure (f x)
  | .hash p _ h => (fun y => y.cast h.symm) <$> hash P (x p)

/-- Sample a uniform value for every node (only the sources' values are used). -/
def sampleAssignment : OracleComp (Spec P) G.Assignment :=
  (List.finRange G.size).foldlM
    (fun z v => Function.update z v <$> sampleBits P (G.len v))
    (fun _ => 0)

/-- Evaluate every node in order; a source takes its value from `z`. -/
def evaluate (z : G.Assignment) : OracleComp (Spec P) G.Assignment :=
  (List.finRange G.size).foldlM
    (fun x v => Function.update x v <$> G.evalNode x v (pure (z v)))
    (fun _ => 0)

/-- Key generation: sample the sources, then evaluate every node. -/
def keygen : OracleComp (Spec P) G.Assignment := do
  let z ← G.sampleAssignment
  G.evaluate z

/-- Root reconstruction: take the given values on `A`, evaluate the other visited nodes, and set
the remaining nodes to zero. -/
def reconstruct (A : Finset (Fin G.size)) (given : G.Assignment) :
    OracleComp (Spec P) G.Assignment :=
  (List.finRange G.size).foldlM
    (fun x v => do
      if v ∈ A then
        return Function.update x v (given v)
      else if G.Visited A v then
        Function.update x v <$> G.evalNode x v (pure 0)
      else
        return Function.update x v 0)
    (fun _ => 0)

/-- The revealed bit string: the values on `A`, in node order. -/
def encode (A : Finset (Fin G.size)) (x : G.Assignment) : List Bool :=
  ((List.finRange G.size).filter fun v => decide (v ∈ A)).flatMap fun v => toBits (x v)

/-- Position of the value of `v` in `encode A`. -/
def offset (A : Finset (Fin G.size)) (v : Fin G.size) : ℕ :=
  ∑ w ∈ A.filter (· < v), G.len w

/-- Parse a revealed bit string into values on `A`. -/
def decode (A : Finset (Fin G.size)) (l : List Bool) : G.Assignment :=
  fun v => ofBits (G.len v) ((l.drop (G.offset A v)).take (G.len v))

end Graph

/-! ## 4. Schemes -/

abbrev Message (P : Params) := BitVec P.msgBits
abbrev Nonce (P : Params) := BitVec P.nonceBits
/-- A signature: a nonce and the revealed bits. -/
abbrev Signature (P : Params) := Nonce P × List Bool
abbrev PublicKey (P : Params) := BitVec P.pkBits

/-- A graph-based one-time signature scheme. -/
structure Scheme (P : Params) where
  /-- The public computation. -/
  graph : Graph P
  /-- The disclosure sets. -/
  sets : Fin P.numSets → Finset (Fin graph.size)
  /-- The verifier must recompute the root. -/
  root_not_mem : ∀ i, graph.root ∉ sets i
  /-- The revealed values suffice: `sets i` meets every path from a secret source to the root. -/
  no_hidden_source :
    ∀ i v, graph.Visited (sets i) v → v ∉ sets i → ¬ (graph.kind v).IsSource
  /-- Signatures reveal at most `maxRevealBits` bits besides the nonce. -/
  reveal_le : ∀ i, graph.revealBits (sets i) ≤ P.maxRevealBits
  /-- Key generation costs at most `keygenBudget`. -/
  keygen_le : graph.keygenCost ≤ P.keygenBudget

/-- The disclosure index selected by message `m` and nonce `η`. -/
def index (P : Params) (m : Message P) (η : Nonce P) : OracleComp (Spec P) ℕ :=
  (fun y => (y.setWidth P.idxBits).toNat) <$> hash P (m ++ η)

namespace Scheme

variable {P : Params} (S : Scheme P)

/-- The public key: a prefix of the root value. -/
def publicKey (x : S.graph.Assignment) : PublicKey P := (x S.graph.root).setWidth P.pkBits

/-- Key generation; the secret key is the value of every node. -/
def keygen : OracleComp (Spec P) (PublicKey P × S.graph.Assignment) := do
  let x ← S.graph.keygen
  return (S.publicKey x, x)

/-- Signing with at most `k` further trials, never retrying a nonce in `tried`. -/
def signLoop (x : S.graph.Assignment) (m : Message P) :
    ℕ → Finset (Nonce P) → OracleComp (Spec P) (Option (Signature P))
  | 0, _ => pure none
  | k + 1, tried =>
    let fresh := Finset.univ \ tried
    if h : 0 < fresh.card then do
      let j ← (liftM ($[0..(fresh.card - 1)]) : OracleComp (Spec P) (Fin (fresh.card - 1 + 1)))
      let η : Nonce P := (fresh.equivFin.symm (Fin.cast (by omega) j)).1
      let i ← index P m η
      if hi : i < P.numSets then
        return some (η, S.graph.encode (S.sets ⟨i, hi⟩) x)
      else
        signLoop x m k (insert η tried)
    else
      pure none

/-- Signing: try uniformly random fresh nonces until one selects a valid index. -/
def sign (x : S.graph.Assignment) (m : Message P) : OracleComp (Spec P) (Option (Signature P)) :=
  S.signLoop x m P.trialLimit ∅

/-- Verification: recompute the index, reconstruct the root, and compare with the public key. -/
def verify (pk : PublicKey P) (m : Message P) (σ : Signature P) : OracleComp (Spec P) Bool := do
  let i ← index P m σ.1
  if hi : i < P.numSets then
    let A := S.sets ⟨i, hi⟩
    if σ.2.length = S.graph.revealBits A then
      let y ← S.graph.reconstruct A (S.graph.decode A σ.2)
      return decide (S.publicKey y = pk)
    else
      return false
  else
    return false

/-- Query cost of verifying a signature at index `i`: the index query, plus reconstruction. -/
def verifyCost (i : Fin P.numSets) : ℕ := idxCost P + S.graph.reconstructCost (S.sets i)

end Scheme

/-! ## 5. Security -/

/-- A one-signature attacker. It may use the random oracle and free randomness throughout. -/
structure Adversary (P : Params) where
  /-- State passed between the two stages. -/
  State : Type
  /-- Given the public key, choose the message to be signed. -/
  choose : PublicKey P → OracleComp (Spec P) (Message P × State)
  /-- Given the signature (`none` if signing failed), output a forgery. -/
  forge : State → Option (Signature P) → OracleComp (Spec P) (Message P × Signature P)

/-- The forgery experiment, including every party's oracle queries. The attacker wins if the
verifier accepts its output and it differs from the pair returned by the signer. -/
def experiment {P : Params} (S : Scheme P) (A : Adversary P) : OracleComp (Spec P) Bool := do
  let (pk, sk) ← S.keygen
  let (m₁, st) ← A.choose pk
  let σ₁ ← S.sign sk m₁
  let (m₂, σ₂) ← A.forge st σ₁
  let ok ← S.verify pk m₂ σ₂
  return ok && decide (σ₁.map (fun s => (m₁, s)) ≠ some (m₂, σ₂))

/-- Security: an attacker whose whole experiment costs at most `B` on every execution path forges
with probability below `B / 2 ^ securityBits`. -/
def Scheme.Secure {P : Params} (S : Scheme P) : Prop :=
  ∀ (A : Adversary P) (B : ℕ), CostAtMost P (experiment S A) B →
    probTrue P (experiment S A) < (B : ℝ≥0∞) / 2 ^ P.securityBits

/-- The forgery experiment of existential unforgeability: the same run, but the attacker wins only
if the verifier accepts its output on a message other than the signed one (or signing failed, so
that no signature was issued at all). Every win here is a win of `experiment`. -/
def weakExperiment {P : Params} (S : Scheme P) (A : Adversary P) : OracleComp (Spec P) Bool := do
  let (pk, sk) ← S.keygen
  let (m₁, st) ← A.choose pk
  let σ₁ ← S.sign sk m₁
  let (m₂, σ₂) ← A.forge st σ₁
  let ok ← S.verify pk m₂ σ₂
  return ok && (σ₁.isNone || decide (m₂ ≠ m₁))

/-- Weak security: the bound of `Secure`, against forgeries on a new message only. It is the
hypothesis of the lower track, which makes a lower bound cover malleable schemes as well. -/
def Scheme.WeaklySecure {P : Params} (S : Scheme P) : Prop :=
  ∀ (A : Adversary P) (B : ℕ), CostAtMost P (weakExperiment S A) B →
    probTrue P (weakExperiment S A) < (B : ℝ≥0∞) / 2 ^ P.securityBits

/-! ## 6. The statement -/

/-- Every weakly secure scheme with parameters `P`, hence every secure one, has a signature index
whose verification costs at least `c` compressions. -/
def VerificationLowerBound (P : Params) (c : ℕ) : Prop :=
  ∀ S : Scheme P, S.WeaklySecure → ∃ i : Fin P.numSets, c ≤ S.verifyCost i

/-- The parameters of the paper. -/
def paperParams : Params where
  hashBits := 256
  blockBits := 512
  pkBits := 128
  msgBits := 256
  nonceBits := 256
  idxBits := 128
  maxRevealBits := 5248
  keygenBudget := 1024
  numSets := 2 ^ 115
  trialLimit := 2 ^ 21
  securityBits := 127

end OptimalOTS
