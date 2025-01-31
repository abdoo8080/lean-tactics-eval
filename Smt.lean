import Auto.EvaluateAuto.TestAuto
import Smt.Auto

def IO.printlnAndFlush {α} [ToString α] (a : α) : IO Unit := do
  IO.println a
  (← IO.getStdout).flush

unsafe def main (args : List String) : IO Unit := do
  let [path] := args | throw $ IO.userError "usage: lake exe smt <path>"
  let line ← IO.FS.readFile path
  let [mod, thm] := line.trim.splitOn " " | throw $ IO.userError "expected: <module> <theorem>"
  let t0 ← IO.monoMsNow
  Lean.initSearchPath (← Lean.findSysroot)
  Lean.withImportModules #[`Smt, `Smt.Real, mod.toName] {} 0 fun env => do
    let t1 ← IO.monoMsNow
    IO.printlnAndFlush s!"[time] load: {t1 - t0}"
    let coreContext := { fileName := "smt", fileMap := default }
    let coreState := { env }
    let (r, _) ← Lean.Core.CoreM.toIO (EvalAuto.runProverOnConst thm.toName Smt.smtSolverFunc) coreContext coreState
    let t2 ← IO.monoMsNow
    IO.printlnAndFlush s!"[time] prove: {t2 - t1}"
    let r ← (Lean.toMessageData r).toString
    IO.println r
