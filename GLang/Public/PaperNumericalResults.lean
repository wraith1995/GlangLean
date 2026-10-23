import GLang.Numerics.Spectral.BasisFSV
import GLang.Numerics.Spectral.BasisSpectralPolynomial
import GLang.Numerics.Pseudoinverse.PseudoInverseCanonical
import GLang.Proofs.Adequacy.Raw.RawGPinvCoordinateBridge

noncomputable section
namespace GLang.PaperNumericalResults
open Classical

theorem spectralProjector_eq_guardedPolynomial
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (S : E →ₗ[ℝ] E) (hS : S.IsSymmetric) (μ : ℝ) :
    BasisSpectral.spectralProjector S μ =
      if Module.End.HasEigenvalue S μ then
        Polynomial.aeval S (BasisSpectral.projectorPolynomial S hS μ) else 0 := by
  classical
  split_ifs with hμ
  · exact (BasisSpectral.projectorPolynomial_eq S hS μ hμ).symm
  · have hbot : Module.End.eigenspace S μ = ⊥ := not_ne_iff.mp hμ
    simp [BasisSpectral.spectralProjector, hbot]

theorem projectedBasisColumns {V W : HSpace}
    {xs : List V.carrier} {ys : List W.carrier}
    (hb : IsListBasis V xs) (hc : IsListBasis W ys)
    (A : V.carrier →ₗ[ℝ] W.carrier) :
    let g := ValuePairedSVD.decomposition (hb.coordMatrix hc A)
      (IsListBasis.gram V xs) (IsListBasis.gram W ys) hb.gram_posDef hc.gram_posDef
    List.ofCoords xs g.U = BasisFSV.fsvLeft V W A (fun μ => decide (μ ≠ 0)) xs ys ∧
    List.ofCoords xs g.UI = BasisFSV.fsvLeft V W A (fun μ => decide (μ = 0)) xs ys ∧
    List.ofCoords ys g.V = BasisFSV.fsvRight V W A (fun μ => decide (μ ≠ 0)) xs ys ∧
    List.ofCoords ys g.VI = BasisFSV.fsvRight V W A (fun μ => decide (μ = 0)) xs ys := by
  simp only [BasisFSV.fsvLeft_of_bases hb hc, BasisFSV.fsvRight_of_bases hb hc]
  exact ⟨ValuePairedSVD.U_ofCoords hb hc A, ValuePairedSVD.UI_ofCoords hb hc A,
    ValuePairedSVD.V_ofCoords hb hc A, ValuePairedSVD.VI_ofCoords hb hc A⟩

theorem pseudoinverse_paired {m n : Nat} (A : Matrix (Fin n) (Fin m) ℝ)
    (G : Matrix (Fin m) (Fin m) ℝ) (H : Matrix (Fin n) (Fin n) ℝ)
    (hG : G.PosDef) (hH : H.PosDef) :
    let g := ValuePairedSVD.decomposition A G H hG hH
    matrixGSVDPinv A G H = g.U * g.sInvMat * g.V.transpose * H := by
  let g := ValuePairedSVD.decomposition A G H hG hH
  exact matrixGSVDPinv_eq_of_decomposition A G H hG hH g
    g.U_orth_MW g.V_orth_MV (ValuePairedSVD.factorization A G H hG hH)

/-- At identity metrics, the same paired formula gives the live ordinary
pseudoinverse, including rectangular and zero-rank inputs. -/
theorem pseudoinverse_standard {m n : Nat} (A : Matrix (Fin n) (Fin m) ℝ) :
    let g := ValuePairedSVD.decomposition A 1 1 Matrix.PosDef.one Matrix.PosDef.one
    matrixSVDPinv A = g.U * g.sInvMat * g.V.transpose := by
  simpa only [matrixGSVDPinv_identity, Matrix.mul_one] using
    pseudoinverse_paired A 1 1 Matrix.PosDef.one Matrix.PosDef.one

/-- The source Moore inverse has exactly the paired-SVD coordinate matrix
in arbitrary ordered bases, with the codomain Gram factor on the right. -/
theorem mooreInverse_coordinates_paired {V W : HSpace}
    {xs : List V.carrier} {ys : List W.carrier}
    (hb : IsListBasis V xs) (hc : IsListBasis W ys)
    (A : V.carrier →ₗ[ℝ] W.carrier) :
    let g := ValuePairedSVD.decomposition (hb.coordMatrix hc A)
      (IsListBasis.gram V xs) (IsListBasis.gram W ys) hb.gram_posDef hc.gram_posDef
    hc.coordMatrix hb (LinearMap.mooreInv V.innerIsIP W.innerIsIP A) =
      g.U * g.sInvMat * g.V.transpose * IsListBasis.gram W ys := by
  rw [IsListBasis.coordMatrix_mooreInv_eq_matrixGSVDPinv hb hc A]
  exact pseudoinverse_paired _ _ _ hb.gram_posDef hc.gram_posDef

theorem pseudoinverse_orthonormalColumns {n k : Nat}
    (Q : Matrix (Fin n) (Fin k) ℝ) (H : Matrix (Fin n) (Fin n) ℝ)
    (hH : H.PosDef) (hQ : Q.transpose * H * Q = 1) :
    matrixGSVDPinv Q 1 H = Q.transpose * H := by
  have hsym : H.transpose = H := by
    simpa only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
      using hH.isHermitian
  apply (matrixGSVDPinv_weightedPenrose Q 1 H Matrix.PosDef.one hH).unique
    Matrix.PosDef.one hH
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [Matrix.mul_assoc, Matrix.mul_one] using congrArg (Q * ·) hQ
  · rw [hQ, Matrix.one_mul]
  · simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hsym, Matrix.mul_assoc]
  · rw [hQ]
    simp

end GLang.PaperNumericalResults
