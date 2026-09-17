import OptimalOTS.Statement
import Submissions.Upper.Main

/-!
# Upper track: the flat scheme, 109 compressions

The flat scheme: 41 hash chains of length 20 whose ends are hashed together into the root
(5248 bits, eleven blocks). All values are 128 bits (separate truncation nodes), the root reads a
separate concatenation node, and the `2 ^ 115` disclosure sets reveal one value per chain so that
the verifier recomputes exactly 96 chain hashes (`Submissions.Upper.Cuts`): reconstruction costs
107 and the index query 2.

* `Submissions.Upper.Scheme`: `Forest.forestScheme : Scheme paperParams`, every signature
  verifies in `109` compressions (`forestScheme_verifyCost`);
* `Submissions.Upper.Main`: `Forest.forestScheme_secure : forestScheme.Secure`, with the bound
  `probTrue ≤ (B - 831) / 2 ^ 127` for every budget `B ≤ 2 ^ 127`.

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

/-- **Cost.** Every signature of the scheme verifies in at most `109` compressions. -/
theorem cost : ∀ i : Fin paperParams.numSets, scheme.verifyCost i ≤ 109 := fun i =>
  (Forest.forestScheme_verifyCost i).le

end OptimalOTS.Challenge.Upper
