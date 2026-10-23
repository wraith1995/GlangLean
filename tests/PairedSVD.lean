import GLang.Numerics.SVD.PairedSVDCoordinates
import GLang.Numerics.Spectral.BasisCanonicalImage
import Lean

open Lean Elab Command

elab "check_paired_svd_axioms" : command => do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in [``GLang.BasisPairedSpectral.right_nonzero_eq_map,
    ``GLang.BasisPairedSpectral.reconstruction,
    ``GLang.BasisPairedSpectral.singularValues_antitone,
    ``GLang.BasisPairedSpectral.image_coordinates_diagonal,
    ``GLang.ValuePairedSVD.decomposition,
    ``GLang.ValuePairedSVD.factorization,
    ``GLang.ValuePairedSVD.image_coordinates,
    ``GLang.ValuePairedSVD.U_ofCoords,
    ``GLang.ValuePairedSVD.UI_ofCoords,
    ``GLang.ValuePairedSVD.V_ofCoords,
    ``GLang.ValuePairedSVD.VI_ofCoords,
    ``GLang.BasisSpectral.standardImageRows_eq_singularValues] do
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless allowed.contains ax do
        throwError "Unexpected axiom in {name}: {ax}"
    logInfo m!"{name}: {axioms}"

check_paired_svd_axioms

-- The paired image of -identity is -u, not the independently chosen +u.
example (V : GLang.HSpace) (u : V.carrier) (hu : V.innerProduct u u = 1) :
    GLang.BasisPairedSpectral.normalizedImage V V (-LinearMap.id) u = -u := by
  letI := V.innerIsIP.toIPSCore
  letI : NormedAddCommGroup V.carrier := V.innerIsIP.toIPSCore.toNormedAddCommGroup
  letI : InnerProductSpace ℝ V.carrier := InnerProductSpace.ofCore inferInstance
  change (Real.sqrt (inner ℝ (-u) (-u)))⁻¹ • (-u) = -u
  change inner ℝ u u = 1 at hu
  simp only [inner_neg_neg, hu, Real.sqrt_one, inv_one, one_smul]
