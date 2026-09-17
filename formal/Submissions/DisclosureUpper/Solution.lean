import OptimalOTS.Statement
import Submissions.DisclosureUpper.Main
import Submissions.DisclosureUpper.Origins

/-!
# Partial-disclosure upper track: the forest scheme, 106 compressions

The scheme of Section 8 of *A Verification Lower Bound for Hash-Based One-Time Signatures*:
63 hash chains of length 14 whose ends are grouped three by three into 21 group digests, grouped
three by three into 7 subtree digests, hashed together into the root. All values are 128 bits
(separate truncation nodes), the grouping hashes read separate concatenation nodes, and the
`2 ^ 115` disclosure sets are cuts of reconstruction cost 105 with at most 41 revealed values,
drawn injectively from the three most common shapes (`Submissions.DisclosureUpper.Cuts`).

* `Submissions.DisclosureUpper.Scheme`: `Forest.forestScheme : Scheme paperParams`, every signature
  verifies in `106` compressions (`forestScheme_verifyCost`);
* `Submissions.DisclosureUpper.Main`: `Forest.forestScheme_secure : forestScheme.Secure`, with the bound
  `probTrue ≤ (B - 912) / 2 ^ 127` for every budget `B ≤ 2 ^ 127`.
* `Submissions.DisclosureUpper.Origins`: at most 41 hash origins per signature, satisfying the
  partial-disclosure framework's bound of 46.

See `README.md` in this directory for the structure of the proof.
-/

open OracleSpec OracleComp ENNReal

noncomputable section

open scoped Classical

set_option linter.constructorNameAsVariable false

namespace OptimalOTS.Challenge.DisclosureUpper

attribute [local irreducible] Forest.forestScheme

/-- **The scheme.** A graph-based one-time signature scheme with the parameters of the paper. -/
noncomputable def scheme : Scheme paperParams := Forest.forestScheme

/-- **Security.** The scheme satisfies the security requirement of the paper. -/
theorem secure : scheme.Secure := Forest.forestScheme_secure

/-- **Cost.** Every signature of the scheme verifies in at most `106` compressions. -/
theorem cost : ∀ i : Fin paperParams.numSets, scheme.verifyCost i ≤ 106 := fun i =>
  (Forest.forestScheme_verifyCost i).le

/-- The payload represents at most 46 underlying hash outputs (in fact, at most 41). -/
theorem disclosure : scheme.DisclosureBound 46 := Forest.forestScheme_disclosureBound46

end OptimalOTS.Challenge.DisclosureUpper
