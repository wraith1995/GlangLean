import GLang.Numerics.SVD.ValueSVD
import Mathlib.LinearAlgebra.Matrix.Rank

/-! The singular-value count agrees with matrix rank, independently of the
chosen factorization. This is the bridge used to present dynamic dimensions
through SVD without changing their error-preserving semantics. -/
namespace GLang
open Matrix
open scoped Matrix

/-- Every SVD factorization has exactly `rank A` positive singular values. -/
theorem SVDecomposition.rank_eq {m n : Nat} (s : SVDecomposition m n)
    (A : Matrix (Fin m) (Fin n) ℝ)
    (hA : A = s.U * Matrix.diagonal s.σ * s.V.transpose) : A.rank = s.r := by
  classical
  have hdiag : (Matrix.diagonal s.σ).rank = s.r := by
    have hnonzero : ∀ i, s.σ i ≠ 0 := fun i => ne_of_gt (s.σ_pos i)
    simp [Matrix.rank_diagonal, hnonzero]
  have hcompress : s.U.transpose * A * s.V = Matrix.diagonal s.σ := by
    calc
      s.U.transpose * A * s.V = (s.U.transpose * s.U) * Matrix.diagonal s.σ * (s.V.transpose * s.V) := by
        rw [hA]
        simp only [Matrix.mul_assoc]
      _ = Matrix.diagonal s.σ := by
        rw [s.U_orthonormal, s.V_orthonormal]
        simp
  apply le_antisymm
  · calc
      A.rank = (s.U * Matrix.diagonal s.σ * s.V.transpose).rank := congrArg Matrix.rank hA
      _ ≤ (s.U * Matrix.diagonal s.σ).rank := Matrix.rank_mul_le_left _ _
      _ ≤ s.U.rank := Matrix.rank_mul_le_left _ _
      _ ≤ s.r := Matrix.rank_le_width _
  · calc
      s.r = (s.U.transpose * A * s.V).rank := by rw [hcompress, hdiag]
      _ ≤ (s.U.transpose * A).rank := Matrix.rank_mul_le_left _ _
      _ ≤ A.rank := Matrix.rank_mul_le_right _ _

/-- The selected SVD exposes the same dimension as the rank-based definition. -/
theorem matrixSVD_rank {m n : Nat} (A : Matrix (Fin m) (Fin n) ℝ) :
    (matrixSVD A).r = A.rank :=
  ((matrixSVD A).rank_eq A (matrixSVD_factor A)).symm

end GLang
