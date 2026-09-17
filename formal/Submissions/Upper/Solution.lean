import OptimalOTS.Statement
import Submissions.Upper.Main

/-!
# Upper track: the forest scheme of the paper, 106 units

The scheme of Section 8 of *A Verification Lower Bound for Hash-Based One-Time Signatures*:
63 hash chains of length 14 whose ends are grouped three by three into 21 group digests, grouped
three by three into 7 subtree digests, hashed together into the root. All values are 128 bits
(separate truncation nodes), the grouping hashes read separate concatenation nodes, and the
`2 ^ 115` disclosure sets are cuts of reconstruction cost 105 with at most 41 revealed values,
drawn injectively from the three most common shapes (`Submissions.Upper.Cuts`).

* `Submissions.Upper.Scheme`: `Forest.forestScheme : Scheme paperParams`, every signature
  verifies in `106` units (`forestScheme_verifyCost`);
* `Submissions.Upper.Main`: `Forest.forestScheme_secure : forestScheme.Secure`, with the bound
  `probTrue ≤ (B - 912) / 2 ^ 127` for every budget `B ≤ 2 ^ 127`.

See `README.md` in this directory for the structure of the proof.
-/

open OracleSpec OracleComp ENNReal

noncomputable section

open scoped Classical

set_option linter.constructorNameAsVariable false

namespace OptimalOTS.Challenge.Upper

attribute [local irreducible] Forest.forestScheme

/-- **The scheme.** A graph-based one-time signature scheme with the parameters of the paper. -/
noncomputable def scheme : Scheme paperParams := Forest.forestScheme

/-- **Security.** The scheme satisfies the security requirement of the paper. -/
theorem secure : scheme.Secure := Forest.forestScheme_secure

/-- **Cost.** Every signature of the scheme verifies in at most `106` hash units. -/
theorem cost : ∀ i : Fin paperParams.numSets, scheme.verifyCost i ≤ 106 := fun i =>
  (Forest.forestScheme_verifyCost i).le

end OptimalOTS.Challenge.Upper
