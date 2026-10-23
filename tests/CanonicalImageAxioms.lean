import GLang.Proofs.Adequacy.Raw.Conversion.RawCobImageSVDs
import Lean

/-! Regression audit: independent canonical image/cokernel choices are related
by the full signed coordinate matrix, evaluated using existing value operators. -/

#print axioms GLang.BasisSpectral.standardImageRows_reconstruct
#print axioms GLang.BasisSpectral.map_canonicalU_column
#print axioms GLang.RawImageCoords.eval
#print axioms GLang.RawCobImageSVDs.raw_arm_cob_image_svds_facts

open Lean Elab Command

elab "check_canonical_image_axioms" : command => do
  let standard := #[``propext, ``Classical.choice, ``Quot.sound]
  let algebra := [``GLang.BasisSpectral.canonicalBlocks_congr,
    ``GLang.BasisSpectral.standardImageRows_reconstruct,
    ``GLang.BasisSpectral.map_canonicalU_column]
  let numerical := [``GLang.RawImageCoords.eval,
    ``GLang.RawCobImageSVDs.raw_arm_cob_image_svds_facts]
  for n in algebra ++ numerical do
    let info ← getConstInfo n
    unless info matches .thmInfo _ do
      throwError "Expected a proved theorem: {n}"
    for ax in ← Lean.collectAxioms n do
      unless standard.contains ax ||
          (numerical.contains n && ax == ``GLang.Matrix.exists_gsvd) do
        throwError "Unexpected canonical image assumption in {n}: {ax}"
  logInfo "Canonical coordinate reconstruction uses foundations only; evaluator and adequacy add at most GSVD existence."

check_canonical_image_axioms
