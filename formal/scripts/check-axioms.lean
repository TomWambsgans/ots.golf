/-
Audit of the protected contract: the definitions that a certificate's meaning depends on must
use only `propext`, `Classical.choice` and `Quot.sound`, and no module of the protected library
may declare an axiom.

    lake env lean scripts/check-axioms.lean
-/
import Lean
import OptimalOTS.Dag
import OptimalOTS.WholeWords
import OptimalOTS.OracleAlgorithm
import OptimalOTS.Riscv

open Lean

/-- The declarations whose meaning fixes what a certificate says. -/
def contractDecls : List Name :=
  [``OptimalOTS.Params, ``OptimalOTS.paperParams,
   ``OptimalOTS.Graph, ``OptimalOTS.Scheme,
   ``OptimalOTS.Scheme.verifyCost, ``OptimalOTS.Graph.reconstructCost,
   ``OptimalOTS.Scheme.Secure, ``OptimalOTS.experiment, ``OptimalOTS.probTrue,
   ``OptimalOTS.CostAtMost, ``OptimalOTS.queryCost, ``OptimalOTS.blockCost, ``OptimalOTS.idxCost,
   ``OptimalOTS.oracleImpl, ``OptimalOTS.Scheme.keygen, ``OptimalOTS.Scheme.sign,
   ``OptimalOTS.Scheme.verify, ``OptimalOTS.index,
   ``OptimalOTS.VerificationLowerBound,
   ``OptimalOTS.Graph.WholeWords,
   ``OptimalOTS.WholeWordVerificationLowerBound,
   ``OptimalOTS.AlgorithmScheme, ``OptimalOTS.AlgorithmScheme.Adversary,
   ``OptimalOTS.AlgorithmScheme.Limits, ``OptimalOTS.AlgorithmScheme.paperLimits,
   ``OptimalOTS.AlgorithmScheme.Admissible, ``OptimalOTS.AlgorithmScheme.Correct,
   ``OptimalOTS.AlgorithmScheme.SigningFailureAtMost,
   ``OptimalOTS.AlgorithmScheme.SignatureSizeAtMost,
   ``OptimalOTS.AlgorithmScheme.RejectsOversized,
   ``OptimalOTS.AlgorithmScheme.KeygenCostAtMost,
   ``OptimalOTS.AlgorithmScheme.SignCostAtMost,
   ``OptimalOTS.AlgorithmScheme.VerifyCostAtMost, ``OptimalOTS.Deterministic,
   ``OptimalOTS.AlgorithmScheme.VerifyDeterministic,
   ``OptimalOTS.AlgorithmScheme.experiment, ``OptimalOTS.AlgorithmScheme.Secure,
   ``OptimalOTS.AlgorithmVerificationLowerBound,
   ``OptimalOTS.Riscv.Image, ``OptimalOTS.Riscv.Image.Valid,
   ``OptimalOTS.Riscv.admittedInstruction, ``OptimalOTS.Riscv.initialState,
   ``OptimalOTS.Riscv.hashInput, ``OptimalOTS.Riscv.hashArgumentsValid,
   ``OptimalOTS.Riscv.writeHash, ``OptimalOTS.Riscv.execute,
   ``OptimalOTS.Riscv.Submission, ``OptimalOTS.Riscv.Submission.scheme,
   ``OptimalOTS.Riscv.Submission.run, ``OptimalOTS.Riscv.Submission.Implements,
   ``OptimalOTS.Riscv.Submission.CostAtMost, ``OptimalOTS.Riscv.Submission.Certificate]

def whitelist : List Name := [``propext, ``Classical.choice, ``Quot.sound]

open Elab.Command in
run_cmd liftCoreM do
  let env ← getEnv
  let mods := env.header.moduleNames
  let mut bad : Array (Name × Name) := #[]
  for (name, ci) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      let modName := mods[idx.toNat]!
      if (`OptimalOTS).isPrefixOf modName && ci.isAxiom then
        bad := bad.push (name, modName)
  unless bad.isEmpty do
    for (n, m) in bad do
      IO.eprintln s!"::error::axiom declaration `{n}` in protected module `{m}`"
    throwError "axiom declarations found in protected modules ({bad.size})"
  IO.println "ok — no axiom is declared in the protected modules"

open Elab.Command in
run_cmd liftTermElabM do
  let mut failed := false
  for decl in contractDecls do
    let axioms ← collectAxioms decl
    let offending := axioms.toList.filter (fun a => !whitelist.contains a)
    unless offending.isEmpty do
      failed := true
      for ax in offending do
        IO.eprintln s!"::error::contract declaration `{decl}` depends on `{ax}`"
  if failed then throwError "the contract depends on non-whitelisted axioms"
  IO.println s!"ok — {contractDecls.length} contract declarations use only propext/Classical.choice/Quot.sound"
