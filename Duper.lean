import Auto.Tactic
import Duper.Tactic
import Auto.EvaluateAuto.TestAuto

def IO.printlnAndFlush {α} [ToString α] (a : α) : IO Unit := do
  IO.println a
  (← IO.getStdout).flush

open Lean Auto in
def duperRaw (lemmas : Array Lemma) (inhs : Array Lemma) : MetaM Expr := do
  let lemmas : Array (Expr × Expr × Array Name × Bool) ← lemmas.mapM
    (fun ⟨⟨proof, ty, _⟩, _⟩ => do return (ty, ← Meta.mkAppM ``eq_true #[proof], #[], true))
  Duper.runDuper lemmas.toList 0

unsafe def main (args : List String) : IO Unit := do
  let [path] := args | throw $ IO.userError "usage: lake exe duper <path>"
  let line ← IO.FS.readFile path
  let [mod, thm] := line.trim.splitOn " " | throw $ IO.userError "expected: <module> <theorem>"
  let t0 ← IO.monoMsNow
  Lean.initSearchPath (← Lean.findSysroot)
  Lean.withImportModules #[`Duper, mod.toName] {} 0 fun env => do
    let t1 ← IO.monoMsNow
    IO.printlnAndFlush s!"[time] load: {t1 - t0}"
    let coreContext := { fileName := "duper", fileMap := default }
    let coreState := { env }
    let (r, _) ← Lean.Core.CoreM.toIO (EvalAuto.runProverOnConst thm.toName duperRaw) coreContext coreState
    let t2 ← IO.monoMsNow
    IO.printlnAndFlush s!"[time] prove: {t2 - t1}"
    let r ← (Lean.toMessageData r).toString
    IO.println r
