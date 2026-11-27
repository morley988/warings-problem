import WaringLinear
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-! A single traversal of the kernel dependency graph of all public project theorems. -/
open Lean Elab Command
run_cmd
  let env ← getEnv
  let prefixes := [`GafniTao, `WaringFieldSmall, `WaringPrior, `WaringLinear, `WaringEnvelope, `WaringDualEnvelope, `WaringSmall, `WaringSharp, `WaringSharpTail,
    `Waring, `WaringSiegel, `WaringLimit, `WaringSmallK, `WaringLocal, `WaringSiegel.SqrtTwoPowerImages]
  let mut targets : Array Name := #[]
  for (n, info) in env.constants.toList do
    if prefixes.any (fun p => p.isPrefixOf n) then
      match info with
      | .thmInfo _ => targets := targets.push n
      | _ => pure ()
  let (_, state) := ((targets.forM CollectAxioms.collect).run env).run {}
  let permitted := [`propext, `Classical.choice, `Quot.sound]
  let extra := state.axioms.filter (fun n => !permitted.contains n)
  unless extra.isEmpty do
    throwError "Unexpected axioms in project theorems: {extra}"
  logInfo m!"Checked the dependency closure of {targets.size} public theorems. Axioms: {state.axioms}"
