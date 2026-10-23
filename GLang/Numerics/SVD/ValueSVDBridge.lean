import GLang.Numerics.SVD.ValueSVD

/-! # SVD / GSVD bridge lemmas

All results here are proved from the spectral construction in `ValueSVD`.
`Adequacy.RawPinvCoordinateBridge` and `RawGPinvCoordinateBridge` connect
these matrix operations to the intrinsic source Moore inverse.
`PseudoInverseCanonical` proves decomposition independence.
-/
namespace GLang
open Matrix

/-- Both ordinary Moore–Penrose projections are symmetric. Together with
MP1 and MP2 in `ValueSVD`, these characterize the inverse. -/
theorem matrixSVDPinv_symm_properties {m n : Nat}
    (A : Matrix (Fin m) (Fin n) ℝ) :
    (A * matrixSVDPinv A).transpose = A * matrixSVDPinv A ∧
    (matrixSVDPinv A * A).transpose = matrixSVDPinv A * A := by
  rw [matrixSVD_mul_pinv, matrixSVD_pinv_mul]
  simp [Matrix.transpose_mul]

/-- The complementary GSVD blocks lie in the kernel and the metric
orthogonal complement of the image, respectively. -/
theorem matrixGSVD_offblock_vanish {m n : Nat}
    (A : Matrix (Fin n) (Fin m) ℝ)
    (M_W : Matrix (Fin m) (Fin m) ℝ)
    (M_V : Matrix (Fin n) (Fin n) ℝ)
    (hW : M_W.PosDef) (hV : M_V.PosDef) :
    A * (matrixGSVD A M_W M_V).UI = 0 ∧
    A.transpose * M_V * (matrixGSVD A M_W M_V).VI = 0 := by
  refine ⟨matrixGSVD_mul_UI A M_W M_V hW hV, ?_⟩
  have hsymm : M_V.transpose = M_V := by
    have h := hV.1
    rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at h
  have h := congrArg Matrix.transpose (matrixGSVD_VIt_MV_mul A M_W M_V hW hV)
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hsymm,
    Matrix.transpose_zero, Matrix.mul_assoc] at h
  rw [Matrix.mul_assoc]
  exact h

/-- Ordinary SVD existence, via identity-metric specialization of the
proved generalized spectral construction. -/
theorem Matrix.svd_via_spectral_theorem (m n : Nat)
    (A : Matrix (Fin m) (Fin n) ℝ) :
    ∃ svd : SVDecomposition m n,
      A = svd.U * Matrix.diagonal svd.σ * svd.V.transpose := by
  exact Matrix.exists_svd m n A

end GLang
