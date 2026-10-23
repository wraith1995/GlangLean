import GLang.Proofs.Value.Presentation.PaperValueDependentReshape
import Lean
open GLang GLang.PaperValueDomains Lean Elab Command
elab "check_dependent_reshape_axioms" : command => do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for n in [``reshape_between_dependent_related, ``reshape_dependent_related,
      ``eval_reshape_dependent_related] do
    let info ← getConstInfo n
    unless info matches .thmInfo _ do
      throwError "Expected a proved theorem: {n}"
    for ax in ← Lean.collectAxioms n do
      unless allowed.contains ax ||
          (n == ``eval_reshape_dependent_related && ax == ``GLang.Matrix.exists_gsvd) do
        throwError "Unexpected dependent reshape assumption in {n}: {ax}"
  logInfo "Conditional full dependent reshape uses foundations only; live wrapper adds at most existing GSVD existence."
check_dependent_reshape_axioms
