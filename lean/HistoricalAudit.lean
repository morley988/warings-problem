import Waring.ValidatedTarget8
import Waring.ValidatedTarget9
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-! The historical endpoints state eventual positive representation with
no analytic premises. The kernel dependency check permits the three
standard mathematical foundations. -/
example : Waring.WaringBound 8 38 := Waring.waring_bound_8_38
example : Waring.WaringBound 9 46 := Waring.waring_bound_9_46

open Lean Elab Command
run_cmd
  let env ← getEnv
  let targets := #[`Waring.waring_bound_8_38, `Waring.waring_bound_9_46]
  let (_, state) := ((targets.forM CollectAxioms.collect).run env).run {}
  let permitted := [`propext, `Classical.choice, `Quot.sound]
  let extra := state.axioms.filter (fun n => !permitted.contains n)
  unless extra.isEmpty do
    throwError "Unexpected axioms in historical Waring endpoints: {extra}"
  logInfo m!"Historical Waring endpoints {targets}. Axioms: {state.axioms}"
