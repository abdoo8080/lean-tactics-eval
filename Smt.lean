import Auto.EvaluateAuto.TestAuto
import Smt.Auto
import Smt.BitVec
import Smt.Bool
import Smt.Builtin
import Smt.Int
import Smt.Nat
import Smt.Options
import Smt.Prop
import Smt.Quant
import Smt.String
import Smt.Tactic
import Smt.UF

unsafe def main (args : List String) : IO Unit := do
  let [path] := args | throw $ IO.userError "usage: lake exe smt <path>"
  let line ← IO.FS.readFile path
  let [mod, thm] := line.trim.splitOn " " | throw $ IO.userError "expected: <module> <theorem>"
  Lean.initSearchPath (← Lean.findSysroot)
  Lean.withImportModules #[`Smt, mod.toName] ({ {} with  }) 0 fun env => do
    let coreContext := { fileName := "smt", fileMap := default }
    let coreState := { env }
    let (r, _) ← Lean.Core.CoreM.toIO (EvalAuto.runProverOnConst thm.toName Smt.smtSolverFunc) coreContext coreState
    let r ← (Lean.toMessageData r).toString
    IO.println r

def test name := do
  let r ← EvalAuto.runProverOnConst name Smt.smtSolverFunc
  Lean.logInfo m!"{r}"

#check Int.add_assoc
-- #eval main ["Int.bmod_mul_bmod"]

set_option trace.smt true in
set_option trace.smt.translate true in
set_option trace.smt.translate.query true in
-- #eval test ``Int.add_assoc
-- #eval test ``Int.bmod_mul_bmod

set_option auto.native true
set_option auto.mono.mode "fol"
-- set_option auto.mono.ciInstDefEq.mode "reducible"
-- set_option auto.mono.termLikeDefEq.mode "reducible"

attribute [rebind Auto.Native.solverFunc] Smt.smtSolverFunc

-- set_option trace.smt true in
-- set_option trace.smt.translate true in
-- set_option trace.smt.translate.query true in
-- example (a b c : Int) : a + b + c = a + (b + c) := by
--   auto [Int.add_assoc.aux1, Int.add_comm, Int.add_assoc.aux2, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

-- set_option auto.smt true
-- set_option auto.smt.solver.name "cvc5"
-- set_option auto.smt.trust true
-- set_option trace.auto.smt.printCommands true

-- example (a b c : Int) : a + b + c = a + (b + c) := by
--   auto [Int.add_assoc.aux1, Int.add_comm, Int.add_assoc.aux2, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

#check Int.succ_neg_succ

def Int.succ (a : Int) := a + 1

set_option trace.smt true in
open Int in
example (a : Int) : succ (-succ a) = -a := by
  smt [Int.succ]
