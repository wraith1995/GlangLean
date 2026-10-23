import GLang.Numerics.Spectral.BasisCanonicalBlocks

namespace GLang
open scoped BigOperators
noncomputable section

namespace BasisSpectral

/-- Equal metrics give the same canonical blocks; positive-definiteness
certificates do not affect the selected vectors. -/
theorem canonicalBlocks_congr {m n : Nat} (A : Matrix (Fin n) (Fin m) ℝ)
    {G G' : Matrix (Fin m) (Fin m) ℝ} {H H' : Matrix (Fin n) (Fin n) ℝ}
    (hG : G.PosDef) (hH : H.PosDef) (hG' : G'.PosDef) (hH' : H'.PosDef)
    (eG : G = G') (eH : H = H') :
    canonicalBlocks A G H hG hH = canonicalBlocks A G' H' hG' hH' := by
  subst G'
  subst H'
  rfl

/-- Source-first storage of the coordinate conversion between paired canonical
singular-vector selections in standard ambient bases. It is the singular-value diagonal. -/
def standardImageRows {m n : Nat} (A : Matrix (Fin n) (Fin m) ℝ) :=
  let g := canonicalBlocks A 1 1 Matrix.PosDef.one Matrix.PosDef.one
  g.U.transpose * A.transpose * g.V

/-- Paired image conversion is exactly the positive singular-value diagonal. -/
theorem standardImageRows_eq_singularValues {m n : Nat}
    (A : Matrix (Fin n) (Fin m) ℝ) :
    standardImageRows A =
      (ValuePairedSVD.decomposition A 1 1 Matrix.PosDef.one Matrix.PosDef.one).sMat := by
  have h := congrArg Matrix.transpose
    (ValuePairedSVD.image_coordinates A 1 1 Matrix.PosDef.one Matrix.PosDef.one)
  change (ValuePairedSVD.decomposition A 1 1 Matrix.PosDef.one Matrix.PosDef.one).U.transpose *
    A.transpose * (ValuePairedSVD.decomposition A 1 1 Matrix.PosDef.one Matrix.PosDef.one).V = _
  rw [Matrix.mul_assoc]
  simpa only [Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.transpose_one, Matrix.mul_one, Matrix.one_mul,
    GSVDecomposition.sMat, Matrix.diagonal_transpose] using h

theorem standardImageRows_reconstruct {m n : Nat}
    (A : Matrix (Fin n) (Fin m) ℝ) :
    let g := canonicalBlocks A 1 1 Matrix.PosDef.one Matrix.PosDef.one
    g.V * (standardImageRows A).transpose = A * g.U := by
  simpa only [standardImageRows, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.mul_assoc, Matrix.mul_one] using
      canonicalBlocks_image_reconstruct A 1 1 Matrix.PosDef.one Matrix.PosDef.one

theorem map_canonicalU_column
    {V0 V1 : HSpace} {S0 : List V0.carrier} {S1 : List V1.carrier}
    (hb0 : IsListBasis V0 S0) (hb1 : IsListBasis V1 S1)
    (f : V0.carrier →ₗ[ℝ] V1.carrier)
    (j : Fin (hb0.coordMatrix hb1 f).rank) :
    let A := hb0.coordMatrix hb1 f
    let g := canonicalBlocks A 1 1 Matrix.PosDef.one Matrix.PosDef.one
    f ((List.ofCoords S0 g.U).get
      (Fin.cast (List.ofCoords_length S0 g.U).symm j)) =
      ∑ i : Fin A.rank, standardImageRows A j i •
        (List.ofCoords S1 g.V).get
          (Fin.cast (List.ofCoords_length S1 g.V).symm i) := by
  dsimp only
  let A := hb0.coordMatrix hb1 f
  let g := canonicalBlocks A 1 1 Matrix.PosDef.one Matrix.PosDef.one
  change f ((List.ofCoords S0 g.U).get _) =
    ∑ i : Fin A.rank, standardImageRows A j i • (List.ofCoords S1 g.V).get _
  rw [List.ofCoords_get]
  simp only [Fin.cast_trans, Fin.cast_eq_self]
  rw [hb0.apply_sum_smul hb1 f, mulVec_col_eq]
  have hmul : hb0.coordMatrix hb1 f * g.U = g.V * (standardImageRows A).transpose :=
    (standardImageRows_reconstruct A).symm
  simp only [List.ofCoords_get, Fin.cast_trans, Fin.cast_eq_self,
    Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  have hentry := congrArg (fun B : Matrix (Fin S1.length) (Fin A.rank) ℝ => B i j) hmul
  change (hb0.coordMatrix hb1 f * g.U) i j =
    ∑ k, g.V i k * standardImageRows A j k at hentry
  calc
    _ = (∑ k, g.V i k * standardImageRows A j k) • S1.get i :=
      congrArg (fun c => c • S1.get i) hentry
    _ = _ := by
      simp only [Finset.sum_smul, mul_comm]
      rfl

end BasisSpectral
end
end GLang
