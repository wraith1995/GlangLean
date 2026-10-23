import GLang.Numerics.SVD.ValueSVDBridge
import GLang.Numerics.Spectral.BasisSpectral
import Lean

open Lean Elab Command

elab "check_spectral_axiom_reduction" : command => do
  let standard := #[``propext, ``Classical.choice, ``Quot.sound]

  for n in [``GLang.matrixSVDPinv_mul_self,
      ``GLang.matrixSVDPinv_mul_self_mul_svdPinv,
      ``GLang.matrixSVDPinv_symm_properties] do
    let info ← getConstInfo n
    unless (match info with | .thmInfo _ => true | _ => false) do
      throwError "Expected a proved theorem: {n}"
    for ax in ← Lean.collectAxioms n do
      unless standard.contains ax || ax == ``GLang.Matrix.exists_gsvd do
        throwError "Unexpected dependency of {n}: {ax}"
  for n in [``GLang.BasisSpectral.normalizedLexInd_orthonormal,
      ``GLang.BasisSpectral.normalizedLexInd_span,
      ``GLang.BasisSpectral.filteredLeft, ``GLang.BasisSpectral.filteredRight] do
    for ax in ← Lean.collectAxioms n do
      unless standard.contains ax do
        throwError "Spectral infrastructure must not use project assumptions: {n}, {ax}"
  logInfo "Three MP assumptions replaced by proofs; spectral infrastructure uses only standard foundations."

check_spectral_axiom_reduction
#print axioms GLang.matrixSVDPinv_symm_properties
