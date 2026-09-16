import OptimalOTS.Statement

/-!
# Oracle tables

`tableImpl P dec g` forwards uniform sampling and answers every hash query `q` from the table
`g : Cell → BitVec hashBits` through the decoding `dec`. `HashQueriesIn dec oa` says that every
hash query of `oa` decodes to a cell.
-/

open OracleSpec OracleComp ENNReal

noncomputable section

open scoped Classical

namespace OptimalOTS

/-- Forward uniform sampling; answer hash queries from the table `g` through the decoding `dec`. -/
def tableImpl (P : Params) {Cell : Type} (dec : Query → Option Cell)
    (g : Cell → BitVec P.hashBits) : QueryImpl (Spec P) ProbComp :=
  (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)) +
    (fun q => (pure (match dec q with
      | some c => g c
      | none => 0) : ProbComp (BitVec P.hashBits)) : QueryImpl (hashSpec P) ProbComp)

/-- Every hash query of `oa` decodes to a cell. -/
def HashQueriesIn {P : Params} {Cell : Type} (dec : Query → Option Cell) {α : Type}
    (oa : OracleComp (Spec P) α) : Prop :=
  oa.AllQueriesSatisfy fun t =>
    match t with
    | .inl _ => True
    | .inr q => (dec q).isSome

end OptimalOTS
