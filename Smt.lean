import Auto.EvaluateAuto.TestAuto
import Smt.Auto

unsafe def main (args : List String) : IO Unit := do
  let [path] := args | throw $ IO.userError "usage: lake exe smt <path>"
  let line ← IO.FS.readFile path
  let [mod, thm] := line.trim.splitOn " " | throw $ IO.userError "expected: <module> <theorem>"
  Lean.initSearchPath (← Lean.findSysroot)
  Lean.withImportModules #[`Smt, `Smt.Real, mod.toName] {} 0 fun env => do
    let coreContext := { fileName := "smt", fileMap := default }
    let coreState := { env }
    let (r, _) ← Lean.Core.CoreM.toIO (EvalAuto.runProverOnConst thm.toName Smt.smtSolverFunc) coreContext coreState
    let r ← (Lean.toMessageData r).toString
    IO.println r
