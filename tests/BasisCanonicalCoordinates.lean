import GLang.Numerics.SVD.ValueCanonicalFSV
import Lean
open Lean Elab Command
open GLang GLang.BasisSpectral GLang.ValueCanonicalFSV
open scoped Matrix

elab "check_canonical_transport_axioms" : command => do
  for n in [``adjoint_intertwines, ``eigenvaluesIncreasing_intertwines,
      ``filteredLeft_map, ``filteredRight_map,
      ``leftVectors_coordinateChart, ``rightVectors_coordinateChart,
      ``leftMatrix_ofCoords, ``rightMatrix_ofCoords,
      ``ValueCanonicalFSV.eval, ``eval_ok, ``eval_success_valid,
      ``ResultMatrix.flatten_get] do
    for ax in ← Lean.collectAxioms n do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected canonical transport/runtime axiom in {n}: {ax}"
  logInfo "Exact filtered transport and checked canonical FSV use only standard Lean axioms."
check_canonical_transport_axioms

example (which : ValFFSProp) :
    eval which 2 3 (FlatArray.zeros 5) (FlatArray.zeros 4) (FlatArray.zeros 9) =
      .error .mismatch := by
  apply eval_shape_mismatch
  norm_num [GSVDInputsShape, FlatArray.zeros]

example (which : ValFFSProp) :
    eval which 1 1 (FlatArray.zeros 1) (FlatArray.zeros 1) (FlatArray.zeros 1) =
      .error .mismatch := by
  apply eval_metric_mismatch
  left
  have hz : denotAsMatrix 1 1 (FlatArray.zeros 1).get = (0 : Matrix (Fin 1) (Fin 1) ℝ) := by
    ext i j
    simp [denotAsMatrix]
  rw [hz]
  have hn := Matrix.posDef_natCast_iff (R := ℝ) (n := Fin 1) (d := 0)
  simpa using hn.not

-- Literal non-square row/column order agrees with the live C-order convention.
example : (ResultMatrix.mk 2 3 !![1, 2, 3; 4, 5, 6]).flatten.get 4 = 5 := by
  change (5 : ℝ) = 5
  rfl

-- Empty output dimensions remain empty.
example : (ResultMatrix.mk 0 3 (fun i => Fin.elim0 i)).flatten.length = 0 := rfl
#print axioms leftMatrix_ofCoords
#print axioms ValueCanonicalFSV.eval
