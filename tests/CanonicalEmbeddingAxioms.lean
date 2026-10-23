import GLang.Proofs.Adequacy.Raw.Terms.RawTermAdequacyEmbed
import Lean

open Lean Elab Command

elab "check_canonical_embedding_axioms" : command => do
  let standard := #[``propext, ``Classical.choice, ``Quot.sound]
  for ax in ← Lean.collectAxioms ``GLang.BasisSpectral.canonicalBlocks_image_reconstruct do
    unless standard.contains ax do
      throwError "Canonical image reconstruction introduced an assumption: {ax}"
  for n in [``GLang.RawTermEmbed.eval_vtrans_canonicalUI,
      ``GLang.RawTermEmbed.eval_vtrans_canonicalU,
      ``GLang.RawTermEmbed.eval_vtrans_canonicalV,
      ``GLang.RawTermEmbed.eval_vtrans_canonicalVI,
      ``GLang.RawTermEmbed.raw_arm_term_embed_kernel_of_numerical,
      ``GLang.RawTermEmbed.raw_arm_term_embed_cokernel_of_numerical,
      ``GLang.RawTermEmbed.raw_arm_term_embed_image_of_numerical,
      ``GLang.RawTermEmbed.raw_arm_term_embed_coimage_of_numerical] do
    let info ← getConstInfo n
    unless (match info with | .thmInfo _ => true | _ => false) do
      throwError "Expected a proved theorem: {n}"
    let axioms ← Lean.collectAxioms n
    logInfo m!"{n}: {axioms}"
    for ax in axioms do
      unless standard.contains ax || ax == ``GLang.Matrix.exists_gsvd do
        throwError "Unexpected numerical embedding assumption in {n}: {ax}"

check_canonical_embedding_axioms
#print axioms GLang.BasisSpectral.canonicalBlocks_image_reconstruct
