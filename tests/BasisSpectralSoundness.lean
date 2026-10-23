import GLang.Numerics.Spectral.BasisSpectralPolynomial
import GLang.Numerics.Spectral.BasisSpectralCoordinates
import GLang.Numerics.Spectral.BasisSpectralTransport
import Lean
open Lean Elab Command

elab "check_canonical_spectral_axioms" : command => do
  for n in [``GLang.BasisSpectral.bucket_span,
      ``GLang.BasisSpectral.filteredLeft_inner, ``GLang.BasisSpectral.filteredRight_inner,
      ``GLang.BasisSpectral.filteredLeft_zero_span, ``GLang.BasisSpectral.filteredLeft_nonzero_span,
      ``GLang.BasisSpectral.filteredRight_zero_span, ``GLang.BasisSpectral.filteredRight_nonzero_span,
      ``GLang.BasisSpectral.filteredLeft_zero_length, ``GLang.BasisSpectral.filteredRight_nonzero_length,
      ``GLang.BasisSpectral.projectorPolynomial_eq,
      ``GLang.BasisSpectral.transitionMatrix_mulVec,
      ``GLang.BasisSpectral.transitionMatrix_transpose_mul,
      ``GLang.BasisSpectral.bucket_map] do
    for ax in ← Lean.collectAxioms n do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom in paper spectral construction {n}: {ax}"
  logInfo "Canonical spectral properties, polynomial projection, and coordinate transport use no project axioms."
check_canonical_spectral_axioms

-- The coordinate bridge retains the sign omitted by a positive singular value.
example : GLang.BasisSpectral.transitionMatrix (fun _ : Fin 1 => (1 : ℝ))
    (fun _ : Fin 1 => (-1 : ℝ)) 0 0 = -1 := by
  simp [GLang.BasisSpectral.transitionMatrix]

#print axioms GLang.BasisSpectral.filteredRight_nonzero_span
#print axioms GLang.BasisSpectral.bucket_map
