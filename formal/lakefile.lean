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

/-- The submission roots. `Submissions.Lower.*` and `Submissions.Upper.*` are the only
modules a submission may add or edit. -/
lean_lib Submissions where
  globs := #[.submodules `Submissions]
