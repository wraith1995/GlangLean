import GLang.Proofs.Value.Partial.PartialValueSVDDimensions
import GLang.Artifact
import Lean
open GLang

example (n : Nat) : (matrixSVD (1 : Matrix (Fin n) (Fin n) ℝ)).r = n := by
  simp [matrixSVD_rank]
example (m n : Nat) : (matrixSVD (0 : Matrix (Fin m) (Fin n) ℝ)).r = 0 := by
  simp [matrixSVD_rank]
example (m n : Nat) (a : FlatArray) (h : a.length ≠ m * n) :
    ffsOperandSVDPartial (.ok [m, n]) (.ok (.array a)) = .error .mismatch := by
  rw [ffsOperandSVDPartial_eq]
  exact ffsOperandRankPartial_wrong_length m n a h
example (p : ValFFSProp) (sh : List Nat) (err : DimError) :
    ffsDimensionSVD p (.ok sh) (.error err) = .error err := by
  rw [ffsDimensionSVD_eq]
  exact ffsDimensionPartial_error p sh err

#print axioms GLang.matrixSVD_rank
#print axioms GLang.ffsDimensionSVD_eq
#print axioms GLang.shapeOf_ffs_svd
