import OptimalOTS.Statement
import OptimalOTS.WholeWords
import Submissions.WholeWordsUpper.Main
import Submissions.WholeWordsUpper.Words

/-!
# Whole-word upper track: the forest scheme with tweak words, 106 compressions

The scheme of Section 8 of *A Verification Lower Bound for Hash-Based One-Time Signatures*
(63 hash chains of length 14 whose ends are grouped three by three into 21 group digests, grouped
three by three into 7 subtree digests, hashed together into the root), written in whole 128-bit
words: every hash input starts with a public constant 128-bit tweak word naming its hash node,
followed by the concatenated 128-bit values it reads, and every value is the low half of its hash
node. A chain step hashes 256 bits and a grouping hash 512 bits (one compression each), the root
1024 bits (two compressions); key generation costs 912 compressions.

* `Submissions.WholeWordsUpper.Words`: `Forest.graph_wholeWords : graph.WholeWords`;
* `Submissions.WholeWordsUpper.Scheme`: every signature verifies in `106` compressions
  (`forestScheme_verifyCost`);
* `Submissions.WholeWordsUpper.Main`: `Forest.forestScheme_secure : forestScheme.Secure`, with the
  bound `probTrue ≤ (B - 912) / 2 ^ 127` for every budget `B ≤ 2 ^ 127`.

See `README.md` in this directory for the construction and the structure of the proof.
-/

open OracleSpec OracleComp ENNReal

noncomputable section

open scoped Classical

set_option linter.constructorNameAsVariable false

namespace OptimalOTS.Challenge.WholeWordsUpper

/-- **The scheme.** A graph-based one-time signature scheme with the parameters of the paper. -/
noncomputable def scheme : Scheme paperParams := Forest.forestScheme

/-- **Whole words.** Every node computes whole 128-bit words. -/
theorem wholeWords : scheme.graph.WholeWords := Forest.graph_wholeWords

/-- **Security.** Strong unforgeability in the shared random-oracle experiment. -/
theorem secure : scheme.Secure := Forest.forestScheme_secure

/-- **Cost.** Every signature of the scheme verifies in at most `106` compressions. -/
theorem cost : ∀ i : Fin paperParams.numSets, scheme.verifyCost i ≤ 106 := fun i =>
  (Forest.forestScheme_verifyCost i).le

end OptimalOTS.Challenge.WholeWordsUpper

/--
info: 'OptimalOTS.Challenge.WholeWordsUpper.wholeWords' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms OptimalOTS.Challenge.WholeWordsUpper.wholeWords
