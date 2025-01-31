import Auto.EvaluateAuto.TestAuto

def IO.printlnAndFlush {α} [ToString α] (a : α) : IO Unit := do
  IO.println a
  (← IO.getStdout).flush

open Lean Auto in
/--
  Run `auto`'s monomorphization and preprocessing, then send the problem to different solvers
-/
def runAuto
  (declName? : Option Name) (lemmas : Array Lemma) (inhFacts : Array Lemma) : MetaM Expr :=
  Meta.withDefault do
    traceLemmas `auto.runAuto.printLemmas s!"All lemmas received by {decl_name%}:" lemmas
    let lemmas ← rewriteIteCondDecide lemmas
    let (proof, _) ← Monomorphization.monomorphize lemmas inhFacts (@id (Reif.ReifM Expr) do
      let s ← get
      let u ← computeMaxLevel s.facts
      (reifMAction s.facts s.inhTys s.inds).run' {u := u})
    trace[auto.tactic] "Auto found proof of {← Meta.inferType proof}"
    trace[auto.tactic.printProof] "{proof}"
    return proof
where
  reifMAction
    (uvalids : Array UMonoFact) (uinhs : Array UMonoFact)
    (minds : Array (Array SimpleIndVal)) : LamReif.ReifM Expr := do
    let exportFacts ← LamReif.reifFacts uvalids
    let mut exportFacts := exportFacts.map (Embedding.Lam.REntry.valid [])
    let _ ← LamReif.reifInhabitations uinhs
    let exportInds ← LamReif.reifMutInds minds
    LamReif.printValuation
    -- **Preprocessing in Verified Checker**
    let (exportFacts', exportInds) ← LamReif.preprocess exportFacts exportInds
    exportFacts := exportFacts'
    -- **SMT**
    if auto.smt.get (← getOptions) then
      let (proof, _) ← querySMT exportFacts exportInds
      if let .some proof := proof then
        return proof
    throwError "Auto failed to find proof"

unsafe def main (args : List String) : IO Unit := do
  let [path] := args | throw $ IO.userError "usage: lake exe smt <path>"
  let line ← IO.FS.readFile path
  let [mod, thm] := line.trim.splitOn " " | throw $ IO.userError "expected: <module> <theorem>"
  let t0 ← IO.monoMsNow
  Lean.initSearchPath (← Lean.findSysroot)
  Lean.withImportModules #[`Auto.Tactic, mod.toName] {} 0 fun env => do
    let t1 ← IO.monoMsNow
    IO.printlnAndFlush s!"[time] load: {t1 - t0}"
    let coreContext := { fileName := "auto", fileMap := default }
    let coreState := { env }
    let (r, _) ← Lean.Core.CoreM.toIO
      (Lean.withOptions (·.setBool ``auto.smt true
                        |>.setString ``auto.smt.solver.name "cvc5"
                        |>.setBool ``auto.smt.trust true
                        |>.setString ``auto.mono.mode "fol"
                        |>.setString ``auto.mono.mode "fol"
                        |>.setNat ``Lean.maxHeartbeats 200000000
                        |>.setNat ``Lean.maxRecDepth 1048576)
      (EvalAuto.runProverOnConst thm.toName (runAuto (.some thm.toName)))) coreContext coreState
    let t2 ← IO.monoMsNow
    IO.printlnAndFlush s!"[time] prove: {t2 - t1}"
    let r ← (Lean.toMessageData r).toString
    IO.println r
