import GLang.Numerics.Spectral.BasisMetricCoordinates
import Lean
open Lean Elab Command
open scoped Matrix

elab "check_canonical_numeric_axioms" : command => do
  for n in [``GLang.BasisSpectral.metricSpace,
      ``GLang.BasisSpectral.kerMatrix, ``GLang.BasisSpectral.cokerMatrix,
      ``GLang.BasisSpectral.imgMatrix, ``GLang.BasisSpectral.coimgMatrix,
      ``GLang.BasisSpectral.leftMatrix_orthonormal,
      ``GLang.BasisSpectral.rightMatrix_orthonormal,
      ``GLang.BasisSpectral.imageConversion_reconstruct,
      ``GLang.BasisSpectral.imageConversion_mulVec,
      ``GLang.BasisSpectral.coordinateChart_basis] do
    for ax in ← Lean.collectAxioms n do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected numerical FSV axiom in {n}: {ax}"
  logInfo "Canonical metric FSV matrices and image conversion use no project axioms."
check_canonical_numeric_axioms

-- Rectangular coordinate reconstruction preserves column order and values.
example : GLang.BasisSpectral.columns [![1, 2], ![3, 4]] *ᵥ ![5, 6] = ![23, 34] := by
  ext i
  change (∑ j : Fin 2, ([![1, 2], ![3, 4]] : List (Fin 2 → ℝ)).get j i * ![5, 6] j) = _
  simp only [Fin.sum_univ_two]
  fin_cases i
  · change (1 * 5 + 3 * 6 : ℝ) = 23
    norm_num
  · change (2 * 5 + 4 * 6 : ℝ) = 34
    norm_num

example : GLang.BasisSpectral.columns ([] : List (Fin 0 → ℝ)) = 0 := by
  ext i
  exact Fin.elim0 i
#print axioms GLang.BasisSpectral.imageConversion_reconstruct
#print axioms GLang.BasisSpectral.coordinateChart
