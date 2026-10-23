import GLang.Proofs.Adequacy.Raw.RawGPinvCoordinateBridge
import GLang.Numerics.Spectral.BasisSpectralMatrices

/-! # Decomposition-independent matrix pseudoinverses

The metric Penrose equations characterize the result, including deficient
rank and repeated singular values. Positive definiteness is essential;
the evaluator's fallback for malformed metrics is not covered by this claim.
-/
namespace GLang
open scoped Matrix

/-- The four Penrose equations with domain metric `G` and codomain metric `H`. -/
structure WeightedPenrose {m n : Nat}
    (A : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin n) ℝ)
    (G : Matrix (Fin m) (Fin m) ℝ) (H : Matrix (Fin n) (Fin n) ℝ) : Prop where
  aba : A * B * A = A
  bab : B * A * B = B
  ab_self : (A * B).transpose * H = H * (A * B)
  ba_self : (B * A).transpose * G = G * (B * A)

private theorem metric_self {n : Nat} (M K : Matrix (Fin n) (Fin n) ℝ)
    (h : K.transpose * M = M * K) (x y : Fin n → ℝ) :
    (K.mulVec x) ⬝ᵥ (M.mulVec y) = x ⬝ᵥ (M.mulVec (K.mulVec y)) := by
  calc
    _ = x ⬝ᵥ (K.transpose.mulVec (M.mulVec y)) := by
      conv_rhs => rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
    _ = x ⬝ᵥ ((K.transpose * M).mulVec y) := by rw [← Matrix.mulVec_mulVec]
    _ = x ⬝ᵥ ((M * K).mulVec y) := by rw [h]
    _ = _ := by rw [Matrix.mulVec_mulVec]

/-- Any matrix satisfying the metric Penrose equations represents the intrinsic inverse. -/
theorem WeightedPenrose.toLin_eq_mooreInv {m n : Nat}
    {A : Matrix (Fin n) (Fin m) ℝ} {B : Matrix (Fin m) (Fin n) ℝ}
    {G : Matrix (Fin m) (Fin m) ℝ} {H : Matrix (Fin n) (Fin n) ℝ}
    (hG : G.PosDef) (hH : H.PosDef) (h : WeightedPenrose A B G H) :
    Matrix.toLin' B = LinearMap.mooreInv
      (BasisSpectral.metricSpace G hG).innerIsIP
      (BasisSpectral.metricSpace H hH).innerIsIP (Matrix.toLin' A) := by
  apply LinearMap.eq_mooreInv_of_penrose
  · simpa only [Matrix.toLin'_mul] using congrArg Matrix.toLin' h.aba
  · simpa only [Matrix.toLin'_mul] using congrArg Matrix.toLin' h.bab
  · intro x y
    simpa only [BasisSpectral.metricSpace, Matrix.toBilin'_apply',
      Matrix.toLin'_apply, Matrix.mulVec_mulVec] using metric_self H (A * B) h.ab_self x y
  · intro x y
    simpa only [BasisSpectral.metricSpace, Matrix.toBilin'_apply',
      Matrix.toLin'_apply, Matrix.mulVec_mulVec] using metric_self G (B * A) h.ba_self x y

/-- Uniqueness needs no full-rank or simple-spectrum assumption. -/
theorem WeightedPenrose.unique {m n : Nat}
    {A : Matrix (Fin n) (Fin m) ℝ} {B C : Matrix (Fin m) (Fin n) ℝ}
    {G : Matrix (Fin m) (Fin m) ℝ} {H : Matrix (Fin n) (Fin n) ℝ}
    (hG : G.PosDef) (hH : H.PosDef)
    (hB : WeightedPenrose A B G H) (hC : WeightedPenrose A C G H) : B = C := by
  apply Matrix.toLin'.injective
  exact (hB.toLin_eq_mooreInv hG hH).trans (hC.toLin_eq_mooreInv hG hH).symm

/-- Every valid generalized singular decomposition gives the same four equations. -/
theorem GSVDecomposition.weightedPenrose {m n : Nat}
    (gs : GSVDecomposition m n) (A : Matrix (Fin n) (Fin m) ℝ)
    (MW : Matrix (Fin m) (Fin m) ℝ) (MV : Matrix (Fin n) (Fin n) ℝ)
    (hMW : MW.transpose = MW) (hMV : MV.transpose = MV)
    (hU : gs.U.transpose * MW * gs.U = 1)
    (hV : gs.V.transpose * MV * gs.V = 1)
    (hfac : A = gs.V * gs.sMat * gs.U.transpose * MW) :
    WeightedPenrose A (gs.U * gs.sInvMat * gs.V.transpose * MV) MW MV := by
  let G := gs.U * gs.sInvMat * gs.V.transpose * MV
  have hG : G = gs.U * gs.sInvMat * gs.V.transpose * MV := rfl
  have hSSi := gs.sMat_mul_sInvMat
  have hSiS := gs.sInvMat_mul_sMat
  have hAG : A * G = gs.V * gs.V.transpose * MV := by
    calc
      A * G =
          (gs.V * gs.sMat * gs.U.transpose * MW) *
            (gs.U * gs.sInvMat * gs.V.transpose * MV) := by rw [hfac, hG]
      _ = gs.V * gs.sMat * (gs.U.transpose * MW * gs.U) *
          gs.sInvMat * gs.V.transpose * MV := by simp only [Matrix.mul_assoc]
      _ = gs.V * (gs.sMat * gs.sInvMat) * gs.V.transpose * MV := by
        rw [hU]
        simp only [Matrix.mul_assoc, Matrix.mul_one]
      _ = gs.V * gs.V.transpose * MV := by rw [hSSi]; simp
  have hGA : G * A = gs.U * gs.U.transpose * MW := by
    calc
      G * A =
          (gs.U * gs.sInvMat * gs.V.transpose * MV) *
            (gs.V * gs.sMat * gs.U.transpose * MW) := by rw [hG, hfac]
      _ = gs.U * gs.sInvMat * (gs.V.transpose * MV * gs.V) *
          gs.sMat * gs.U.transpose * MW := by simp only [Matrix.mul_assoc]
      _ = gs.U * (gs.sInvMat * gs.sMat) * gs.U.transpose * MW := by
        rw [hV]
        simp only [Matrix.mul_assoc, Matrix.mul_one]
      _ = gs.U * gs.U.transpose * MW := by rw [hSiS]; simp
  have hMP1 : A * G * A = A := by
    calc
      A * G * A = gs.V * (gs.V.transpose * MV * gs.V) *
          gs.sMat * gs.U.transpose * MW := by
        rw [hAG, hfac]
        simp only [Matrix.mul_assoc]
      _ = gs.V * gs.sMat * gs.U.transpose * MW := by rw [hV]; simp
      _ = A := hfac.symm
  have hMP2 : G * A * G = G := by
    calc
      G * A * G = gs.U * (gs.U.transpose * MW * gs.U) *
          gs.sInvMat * gs.V.transpose * MV := by
        rw [hGA, hG]
        simp only [Matrix.mul_assoc]
      _ = gs.U * gs.sInvMat * gs.V.transpose * MV := by rw [hU]; simp
      _ = G := hG.symm
  have hAGSelf : (A * G).transpose * MV = MV * (A * G) := by
    rw [hAG]
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hMV]
    noncomm_ring
  have hGASelf : (G * A).transpose * MW = MW * (G * A) := by
    rw [hGA]
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hMW]
    noncomm_ring
  exact ⟨hMP1, hMP2, hAGSelf, hGASelf⟩

/-- The live generalized inverse satisfies the weighted Penrose equations. -/
theorem matrixGSVDPinv_weightedPenrose {m n : Nat}
    (A : Matrix (Fin n) (Fin m) ℝ)
    (G : Matrix (Fin m) (Fin m) ℝ) (H : Matrix (Fin n) (Fin n) ℝ)
    (hG : G.PosDef) (hH : H.PosDef) :
    WeightedPenrose A (matrixGSVDPinv A G H) G H := by
  apply (matrixGSVD A G H).weightedPenrose A G H
  · simpa only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
      using hG.isHermitian
  · simpa only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
      using hH.isHermitian
  · exact matrixGSVD_U_orth A G H hG hH
  · exact matrixGSVD_V_orth A G H hG hH
  · exact matrixGSVD_factor A G H hG hH

/-- Replacing the chosen GSVD by any valid decomposition preserves the result. -/
theorem matrixGSVDPinv_eq_of_decomposition {m n : Nat}
    (A : Matrix (Fin n) (Fin m) ℝ)
    (G : Matrix (Fin m) (Fin m) ℝ) (H : Matrix (Fin n) (Fin n) ℝ)
    (hG : G.PosDef) (hH : H.PosDef) (gs : GSVDecomposition m n)
    (hU : gs.U.transpose * G * gs.U = 1)
    (hV : gs.V.transpose * H * gs.V = 1)
    (hfac : A = gs.V * gs.sMat * gs.U.transpose * G) :
    matrixGSVDPinv A G H = gs.U * gs.sInvMat * gs.V.transpose * H := by
  apply (matrixGSVDPinv_weightedPenrose A G H hG hH).unique hG hH
  apply gs.weightedPenrose A G H _ _ hU hV hfac
  · simpa only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
      using hG.isHermitian
  · simpa only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
      using hH.isHermitian

/-- The ordinary inverse is the identity-metric Penrose solution. -/
theorem matrixSVDPinv_weightedPenrose {m n : Nat}
    (A : Matrix (Fin n) (Fin m) ℝ) :
    WeightedPenrose A (matrixSVDPinv A) 1 1 := by
  refine ⟨matrixSVDPinv_mul_self A, matrixSVDPinv_mul_self_mul_svdPinv A, ?_, ?_⟩
  · simpa using (matrixSVDPinv_symm_properties A).1
  · simpa using (matrixSVDPinv_symm_properties A).2

/-- Generalized and ordinary inversion agree exactly at identity metrics. -/
theorem matrixGSVDPinv_identity {m n : Nat}
    (A : Matrix (Fin n) (Fin m) ℝ) : matrixGSVDPinv A 1 1 = matrixSVDPinv A := by
  exact (matrixGSVDPinv_weightedPenrose A 1 1 Matrix.PosDef.one Matrix.PosDef.one).unique
    Matrix.PosDef.one Matrix.PosDef.one (matrixSVDPinv_weightedPenrose A)

/-- Any ordinary singular decomposition gives the same inverse matrix. -/
theorem matrixSVDPinv_eq_of_decomposition {m n : Nat}
    (A : Matrix (Fin m) (Fin n) ℝ) (s : SVDecomposition m n)
    (hfac : A = s.U * Matrix.diagonal s.σ * s.V.transpose) :
    matrixSVDPinv A = s.V * s.sigmaInvMat * s.U.transpose := by
  let B := s.V * s.sigmaInvMat * s.U.transpose
  have hAB : A * B = s.U * s.U.transpose := by
    calc
      A * B = s.U * Matrix.diagonal s.σ * (s.V.transpose * s.V) *
          s.sigmaInvMat * s.U.transpose := by rw [hfac]; simp [B, Matrix.mul_assoc]
      _ = s.U * (Matrix.diagonal s.σ * s.sigmaInvMat) * s.U.transpose := by
        rw [s.V_orthonormal]; simp [Matrix.mul_assoc]
      _ = _ := by rw [s.sigma_mul_inverse]; simp
  have hBA : B * A = s.V * s.V.transpose := by
    calc
      B * A = s.V * s.sigmaInvMat * (s.U.transpose * s.U) *
          Matrix.diagonal s.σ * s.V.transpose := by rw [hfac]; simp [B, Matrix.mul_assoc]
      _ = s.V * (s.sigmaInvMat * Matrix.diagonal s.σ) * s.V.transpose := by
        rw [s.U_orthonormal]; simp [Matrix.mul_assoc]
      _ = _ := by rw [s.inverse_mul_sigma]; simp
  apply (matrixSVDPinv_weightedPenrose A).unique Matrix.PosDef.one Matrix.PosDef.one
  refine ⟨?_, ?_, ?_, ?_⟩
  · change A * B * A = A
    rw [hAB]
    calc
      _ = s.U * (s.U.transpose * s.U) * Matrix.diagonal s.σ * s.V.transpose := by
        rw [hfac]; simp only [Matrix.mul_assoc]
      _ = A := by rw [s.U_orthonormal]; simpa using hfac.symm
  · change B * A * B = B
    rw [hBA]
    calc
      _ = s.V * (s.V.transpose * s.V) * s.sigmaInvMat * s.U.transpose := by
        simp only [B, Matrix.mul_assoc]
      _ = B := by rw [s.V_orthonormal]; simp [B]
  · change (A * B).transpose * 1 = 1 * (A * B)
    rw [hAB]; simp [Matrix.transpose_mul]
  · change (B * A).transpose * 1 = 1 * (B * A)
    rw [hBA]; simp [Matrix.transpose_mul]

/-- Ordinary inversion commutes with transposition, including rectangular matrices. -/
theorem matrixSVDPinv_transpose {m n : Nat}
    (A : Matrix (Fin m) (Fin n) ℝ) :
    matrixSVDPinv A.transpose = (matrixSVDPinv A).transpose := by
  apply (matrixSVDPinv_weightedPenrose A.transpose).unique Matrix.PosDef.one Matrix.PosDef.one
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [Matrix.transpose_mul, Matrix.mul_assoc] using
      congrArg Matrix.transpose (matrixSVDPinv_mul_self A)
  · simpa only [Matrix.transpose_mul, Matrix.mul_assoc] using
      congrArg Matrix.transpose (matrixSVDPinv_mul_self_mul_svdPinv A)
  · simpa only [Matrix.mul_one, Matrix.one_mul, ← Matrix.transpose_mul,
      Matrix.transpose_transpose] using (matrixSVDPinv_symm_properties A).2.symm
  · simpa only [Matrix.mul_one, Matrix.one_mul, ← Matrix.transpose_mul,
      Matrix.transpose_transpose] using (matrixSVDPinv_symm_properties A).1.symm

end GLang
