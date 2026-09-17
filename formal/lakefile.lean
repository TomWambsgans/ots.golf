import Lake
open Lake DSL

package OptimalOTS where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]

require VCVio from git
  "https://github.com/Verified-zkEVM/VCVio" @ "25f26bfee60d6700644eb1a69f091091948f15da"

/-- The protected library: the statement and the (rendered) challenge stubs. -/
@[default_target] lean_lib OptimalOTS where
  globs := #[.submodules `OptimalOTS]

/-- A submission may add or edit only the root assigned to its track in `challenges.json`. -/
lean_lib Submissions where
  globs := #[.submodules `Submissions]
