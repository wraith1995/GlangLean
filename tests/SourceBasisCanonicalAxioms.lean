import GLang.Proofs.Source.BasisSoundness
import GLang.Proofs.Basis.BasisStandardFixed
import Lean

open Lean Elab Command

/-- The live source-basis API must not inherit numerical decomposition assumptions. -/
elab "check_source_basis_canonical_axioms" : command => do
  let standard := #[``propext, ``Classical.choice, ``Quot.sound]
  for n in [``GLang.BasisFSV.fsvLeft, ``GLang.BasisFSV.fsvRight,
      ``GLang.BasisFSV.fsvLeft_eq_canonicalUI,
      ``GLang.BasisFSV.fsvLeft_eq_canonicalU,
      ``GLang.BasisFSV.fsvRight_eq_canonicalV,
      ``GLang.BasisFSV.fsvRight_eq_canonicalVI,
      ``GLang.denotBasis, ``GLang.denotBasis_isBasis,
      ``GLang.denotBasis_atSpace_isListBasis,
      ``GLang.denotBasis_orthonormal_of_isStd,
      ``GLang.stdBasis_atSpace_orthonormal,
      ``GLang.Basis.BasisValid.std_tof_eq] do
    for ax in ← Lean.collectAxioms n do
      unless standard.contains ax do
        throwError "Unexpected source-basis assumption in {n}: {ax}"
  logInfo "Live source basis denotation, soundness and standardness use only standard foundations."

check_source_basis_canonical_axioms
#print axioms GLang.denotBasis_isBasis
#print axioms GLang.denotBasis_orthonormal_of_isStd
#print axioms GLang.stdBasis_atSpace_orthonormal
#print axioms GLang.Basis.BasisValid.std_tof_eq
