import VCVio.OracleComp.QueryTracking.RandomOracle.Basic
import VCVio.OracleComp.QueryTracking.QueryBound.Basic
import VCVio.OracleComp.Constructions.SampleableType
import VCVio.OracleComp.SimSemantics.Append
import VCVio.OracleComp.ProbComp
import VCVio.EvalDist.BitVec

/-!
# The DAG signature contract

A scheme is a public computation graph with secret sources, deterministic nodes and hash nodes.
A signature discloses a cut of the graph; verification reconstructs the root and checks its
public-key bits. All parties share one random oracle on bit strings, without implicit labels
or domain separation. Uniform sampling and deterministic computation are free; every hash query
is charged for its complete input, including repeated queries.

An upper bound `c` is a scheme `S` with `S.Secure` and `∀ i, S.verifyCost i ≤ c`; a lower bound
`c` is `VerificationLowerBound P c`. `paperParams` fixes the competition's parameters.
-/

open OracleSpec OracleComp ENNReal

noncomputable section

open scoped Classical

namespace OptimalOTS

/-! ## 1. Parameters -/

/-- Lengths (in bits), resource limits (in compressions) and the security level. -/
structure Params where
  /-- Output length of the random oracle. -/
  hashBits : ℕ
  /-- Input bits per compression block. For positive `blockBits`, hashing `k` bits costs
  `max 1 ⌈k / blockBits⌉`. -/
  blockBits : ℕ
  /-- Public-key length; the public key is the low `pkBits` bits of the root value. -/
  pkBits : ℕ
  /-- Length of messages. -/
  msgBits : ℕ
  /-- Length of signing nonces. -/
  nonceBits : ℕ
  /-- Number of low bits of `H(m ‖ η)` read as the disclosure index. -/
  idxBits : ℕ
  /-- Maximal number of revealed bits in a signature, excluding the nonce. -/
  maxRevealBits : ℕ
  /-- Maximal query cost of key generation. -/
  keygenBudget : ℕ
  /-- Number of disclosure sets. -/
  numSets : ℕ
  /-- Maximal number of nonces tried by the signer. -/
  trialLimit : ℕ
  /-- Security level; see `Scheme.Secure`. -/
  securityBits : ℕ

/-! ## 2. The random oracle and the cost of a query -/

/-- A bit string of any length, used as a random-oracle input. There are no implicit labels or
tweaks: equal strings share an answer, including across graph and index queries. Explicit prefixes
are part of the input and incur their full query cost. -/
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
  /-- The root; its value is resized to `pkBits` to obtain the public key. -/
  root : Fin size
  root_isHash : (kind root).IsHash

/-- The bits of `x`, least significant first. -/
def toBits {n : ℕ} (x : BitVec n) : List Bool := List.ofFn fun i : Fin n => x.getLsbD i

/-- Interpret the list least significant bit first, truncating or zero-extending to `n` bits. -/
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

/-- Read each node's value at its offset in the disclosure string. Reconstruction uses these
values only on `A`; values outside `A` need not have a meaningful decoding. -/
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

/-- Resize the root value to `pkBits`: truncation keeps the low bits; extension pads with zeros. -/
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

/-- Try at most `trialLimit` distinct uniform nonces; return `none` if none selects a valid index. -/
def sign (x : S.graph.Assignment) (m : Message P) : OracleComp (Spec P) (Option (Signature P)) :=
  S.signLoop x m P.trialLimit ∅

/-- Reject invalid indices or payload lengths; otherwise reconstruct the root and compare its
public-key bits with `pk`. -/
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

/-- Verification cost at a valid index and payload length: the index query plus reconstruction.
The cost depends on the disclosure set, not on the supplied values or the final verdict. -/
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

/-- Strong-forgery experiment. The attacker wins when its pair is accepted and differs from the
signed pair; after signing failure, any accepted pair wins. All parties share one oracle table. -/
def experiment {P : Params} (S : Scheme P) (A : Adversary P) : OracleComp (Spec P) Bool := do
  let (pk, sk) ← S.keygen
  let (m₁, st) ← A.choose pk
  let σ₁ ← S.sign sk m₁
  let (m₂, σ₂) ← A.forge st σ₁
  let ok ← S.verify pk m₂ σ₂
  return ok && decide (σ₁.map (fun s => (m₁, s)) ≠ some (m₂, σ₂))

/-- Strong unforgeability: for every attacker and pathwise budget `B` for the entire experiment,
the probability of an accepted fresh pair is strictly below `B / 2 ^ securityBits`. -/
def Scheme.Secure {P : Params} (S : Scheme P) : Prop :=
  ∀ (A : Adversary P) (B : ℕ), CostAtMost P (experiment S A) B →
    probTrue P (experiment S A) < (B : ℝ≥0∞) / 2 ^ P.securityBits

/-! ## 6. The lower bound and paper parameters -/

/-- Every secure scheme with parameters `P` has a signature index whose verification costs at
least `c` compressions. -/
def VerificationLowerBound (P : Params) (c : ℕ) : Prop :=
  ∀ S : Scheme P, S.Secure → ∃ i : Fin P.numSets, c ≤ S.verifyCost i

/-- The competition's parameters. -/
def paperParams : Params where
  hashBits := 256
  blockBits := 512
  pkBits := 128
  msgBits := 256
  nonceBits := 128
  idxBits := 128
  maxRevealBits := 5248
  keygenBudget := 1024
  numSets := 2 ^ 115
  trialLimit := 2 ^ 20
  securityBits := 127

end OptimalOTS
