import Auto.Tactic
import Duper.Tactic
import Auto.EvaluateAuto.TestAuto

open Lean Auto in
def duperRaw (lemmas : Array Lemma) (inhs : Array Lemma) : MetaM Expr := do
  let lemmas : Array (Expr × Expr × Array Name × Bool) ← lemmas.mapM
    (fun ⟨⟨proof, ty, _⟩, _⟩ => do return (ty, ← Meta.mkAppM ``eq_true #[proof], #[], true))
  Duper.runDuper lemmas.toList 0

unsafe def main (args : List String) : IO Unit := do
  let [path] := args | throw $ IO.userError "usage: lake exe duper <path>"
  let line ← IO.FS.readFile path
  let [mod, thm] := line.trim.splitOn " " | throw $ IO.userError "expected: <module> <theorem>"
  Lean.initSearchPath (← Lean.findSysroot)
  Lean.withImportModules #[`Duper, mod.toName] {} 0 fun env => do
    let coreContext := { fileName := "duper", fileMap := default }
    let coreState := { env }
    let (r, _) ← Lean.Core.CoreM.toIO (EvalAuto.runProverOnConst thm.toName duperRaw) coreContext coreState
    let r ← (Lean.toMessageData r).toString
    IO.println r

-- #eval main ["benchmarks/Mathlib.Algebra.AddConstMap.EquivAddConstEquiv.refl_apply"]
-- #eval main ["benchmarks/Mathlib.Topology.UniformSpace.SeparationSeparationQuotient.uniformContinuous_lift"]
