import GLang.Proofs.Value.Presentation.PaperValueNumericSubstitution
import Lean
open GLang GLang.PaperValueDomains
open Lean Elab Command

-- This theorem covers the complete numerical constructor family, including
-- sum-list truncation, all strict shape guards, and every error branch.
elab "check_numeric_substitution_axioms" : command => do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound, ``GLang.Matrix.exists_gsvd]
  for ax in ← Lean.collectAxioms ``arrayPrimitive_eval_subst do
    unless allowed.contains ax do
      throwError "Unexpected numerical substitution assumption: {ax}"
  logInfo "All numerical substitution steps inherit only the existing GSVD axiom."
check_numeric_substitution_axioms
