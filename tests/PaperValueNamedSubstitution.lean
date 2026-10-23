import GLang.Proofs.Value.Presentation.PaperValueNamedSubstContext
import GLang.Proofs.Value.Presentation.PaperValueSubstitutionInference
import GLang.Proofs.Value.Presentation.PaperValueSubstitutionQueries
import Lean
open GLang GLang.PaperValueDomains
open Lean Elab Command

elab "check_named_substitution_steps" : command => do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound, ``GLang.Matrix.exists_gsvd]
  for n in [``NamedSubstCtx.of_fresh, ``NamedSubstCtx.extend,
      ``ValHasType.inferType_subst, ``ValHasType.inferSpace_subst,
      ``original_primitive_subst_output, ``original_primitive_subst_queries] do
    for ax in ← Lean.collectAxioms n do
      unless allowed.contains ax do
        throwError "Unexpected named-substitution step assumption {n}: {ax}"
  logInfo "Original typing substitution steps inherit only existing GSVD existence."
check_named_substitution_steps
