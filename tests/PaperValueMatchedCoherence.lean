import GLang.Proofs.Value.Presentation.PaperValueMatchedCoherence
import GLang.Proofs.Value.Presentation.PaperValueMatchedBinders
import Lean
open GLang GLang.PaperValueDomains Lean Elab Command
elab "check_matched_coherence_axioms" : command => do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for n in [``matchedCoherence_opening, ``MatchedContextRelated.update_opening,
      ``typeCoherent_of_matched_step, ``contextRelated_of_matched_step,
      ``matched_lambda_step, ``matched_pi_step] do
    for ax in ← Lean.collectAxioms n do
      unless allowed.contains ax ||
          ((n == ``matched_lambda_step || n == ``matched_pi_step) && ax == ``GLang.Matrix.exists_gsvd) do
        throwError "Unexpected matched-coherence assumption in {n}: {ax}"
  logInfo "Matched dependent coherence/binders use foundations and at most existing numerical GSVD."
check_matched_coherence_axioms
