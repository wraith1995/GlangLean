import GLang.Artifact
import Lean

open GLang Lean Meta Elab Command

namespace PaperApplicationKindRules

run_cmd liftTermElabM do
  let info ← getConstInfoInduct ``RuntimeValue.ValHasType
  if info.ctors.contains `GLang.RuntimeValue.ValHasType.appV_nonfun then
    throwError "Non-function application must not have a value typing rule"
  let reshape ← getConstInfo ``RuntimeValue.ValHasType.reshap
  forallTelescope reshape.type fun xs _ => do
    let mut kinds : Array Expr := #[]
    for x in xs do
      let t := (← x.fvarId!.getDecl).type
      if t.isAppOfArity ``RuntimeValue.ValTValid 3 then
        kinds := kinds.push t.getAppArgs[2]!
    unless kinds.size == 2 && kinds[0]! == kinds[1]! do
      throwError "The declared reshape source and target must share their kind"

end PaperApplicationKindRules
