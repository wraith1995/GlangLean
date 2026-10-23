import GLang.Proofs.Adequacy.Partial.Functions.PartialSourceFrames
import Lean.Util.CollectAxioms

open Lean Elab Command in
elab "check_partial_source_application_axioms" : command => do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for n in [``GLang.PartialAdequacy.Agree.instantiate_src,
      ``GLang.PartialAdequacy.DimsAt.instantiate_src,
      ``GLang.PartialAdequacy.inferType_domain_dims,
      ``GLang.PartialAdequacy.inferType_domain_sameShape,
      ``GLang.PartialAdequacy.applyAt_agree,
      ``GLang.PartialAdequacy.partialAppNVal_result,
      ``GLang.PartialAdequacy.arm_appN_val,
      ``GLang.PartialAdequacy.arm_frame_reanchor,
      ``GLang.PartialAdequacy.arm_frame_eta] do
    for ax in ← Lean.collectAxioms n do
      unless allowed.contains ax do
        throwError "Unexpected partial source application axiom {n}: {ax}"
  logInfo "Partial higher-order source application and frames retain only the standard logical foundations."
check_partial_source_application_axioms
