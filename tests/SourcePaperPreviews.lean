import GLang.Artifact
import Lean
open Lean Meta Elab Command

run_cmd liftTermElabM do
  let info ← getConstInfo ``GLang.PaperSourceResults.innerProduct
  forallTelescope info.type fun xs _ => do
    let types ← xs.mapM fun x => return (← inferType x)
    unless types.any (fun t => t.isAppOf ``GLang.IofFresh) do
      throwError "Paper notation must not remove the exact Lean freshness premise"

#print axioms GLang.PaperSourceResults.innerProduct
#print axioms GLang.PaperSourceResults.sourceSoundness
