import GLang.Proofs.Adequacy.Raw.RawPinvCoordinateBridge

namespace GLang

open scoped Matrix

/-- A GSVD singular-value diagonal followed by its reciprocal diagonal is
the identity on the rank index. -/
theorem GSVDecomposition.sMat_mul_sInvMat {m n : Nat}
    (g : GSVDecomposition m n) : g.sMat * g.sInvMat = 1 := by
  rw [GSVDecomposition.sMat, GSVDecomposition.sInvMat,
    Matrix.diagonal_mul_diagonal]
  ext i j
  simp only [Matrix.diagonal_apply, Matrix.one_apply]
  by_cases h : i = j
  · subst j
    simp only [↓reduceIte]
    exact mul_inv_cancel₀ (ne_of_gt (g.σ_pos i))
  · simp only [h, ↓reduceIte]

/-- The reciprocal singular-value diagonal is also a left inverse. -/
theorem GSVDecomposition.sInvMat_mul_sMat {m n : Nat}
    (g : GSVDecomposition m n) : g.sInvMat * g.sMat = 1 := by
  rw [GSVDecomposition.sMat, GSVDecomposition.sInvMat,
    Matrix.diagonal_mul_diagonal]
  ext i j
  simp only [Matrix.diagonal_apply, Matrix.one_apply]
  by_cases h : i = j
  · subst j
    simp only [↓reduceIte]
    exact inv_mul_cancel₀ (ne_of_gt (g.σ_pos i))
  · simp only [h, ↓reduceIte]

/-- Coordinate form of self-adjointness relative to a Gram matrix. -/
private theorem metric_dotProduct_self
    {n : Nat} (M H : Matrix (Fin n) (Fin n) ℝ)
    (hH : H.transpose * M = M * H) (x y : Fin n → ℝ) :
    (H.mulVec x) ⬝ᵥ (M.mulVec y) =
      x ⬝ᵥ (M.mulVec (H.mulVec y)) := by
  calc
    (H.mulVec x) ⬝ᵥ (M.mulVec y) =
        x ⬝ᵥ (H.transpose.mulVec (M.mulVec y)) := by
      conv_rhs => rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
    _ = x ⬝ᵥ ((H.transpose * M).mulVec y) := by
      rw [← Matrix.mulVec_mulVec]
    _ = x ⬝ᵥ ((M * H).mulVec y) := by rw [hH]
    _ = x ⬝ᵥ (M.mulVec (H.mulVec y)) := by
      rw [Matrix.mulVec_mulVec]

/-- A Gram-self-adjoint coordinate matrix represents a self-adjoint linear
map in the underlying Hilbert-space bilinear form. -/
private theorem IsListBasis.innerProduct_self_of_coordMatrix
    {V : HSpace} {vs : List V.carrier}
    (hb : IsListBasis V vs) (h : V.carrier →ₗ[ℝ] V.carrier)
    (H : Matrix (Fin vs.length) (Fin vs.length) ℝ)
    (hcoord : hb.coordMatrix hb h = H)
    (hself : H.transpose * IsListBasis.gram V vs =
      IsListBasis.gram V vs * H) :
    ∀ x y, V.innerProduct (h x) y = V.innerProduct x (h y) := by
  intro x y
  have hx : h x = ∑ i, (H.mulVec (hb.coords x)) i • vs.get i := by
    calc
      h x = h (∑ i, hb.coords x i • vs.get i) := by
        rw [hb.sum_coords_smul]
      _ = ∑ i, ((hb.coordMatrix hb h).mulVec (hb.coords x)) i •
          vs.get i := hb.apply_sum_smul hb h (hb.coords x)
      _ = ∑ i, (H.mulVec (hb.coords x)) i • vs.get i := by rw [hcoord]
  have hy : h y = ∑ i, (H.mulVec (hb.coords y)) i • vs.get i := by
    calc
      h y = h (∑ i, hb.coords y i • vs.get i) := by
        rw [hb.sum_coords_smul]
      _ = ∑ i, ((hb.coordMatrix hb h).mulVec (hb.coords y)) i •
          vs.get i := hb.apply_sum_smul hb h (hb.coords y)
      _ = ∑ i, (H.mulVec (hb.coords y)) i • vs.get i := by rw [hcoord]
  calc
    V.innerProduct (h x) y = V.innerProduct
        (∑ i, (H.mulVec (hb.coords x)) i • vs.get i)
        (∑ i, hb.coords y i • vs.get i) := by rw [hx, hb.sum_coords_smul]
    _ = (H.mulVec (hb.coords x)) ⬝ᵥ
        ((IsListBasis.gram V vs).mulVec (hb.coords y)) :=
      IsListBasis.innerProduct_sum_smul V vs _ _
    _ = hb.coords x ⬝ᵥ
        ((IsListBasis.gram V vs).mulVec (H.mulVec (hb.coords y))) :=
      metric_dotProduct_self _ _ hself _ _
    _ = V.innerProduct
        (∑ i, hb.coords x i • vs.get i)
        (∑ i, (H.mulVec (hb.coords y)) i • vs.get i) :=
      (IsListBasis.innerProduct_sum_smul V vs _ _).symm
    _ = V.innerProduct x (h y) := by rw [hb.sum_coords_smul, hy]

/-- In arbitrary list bases, the corrected Gram-weighted GSVD formula
`U * S⁻¹ * Vᵀ * M_V` is exactly the coordinate matrix of the intrinsic
Moore inverse. -/
theorem IsListBasis.coordMatrix_mooreInv_eq_matrixGSVDPinv
    {V0 V1 : HSpace} {vs0 : List V0.carrier} {vs1 : List V1.carrier}
    (hb0 : IsListBasis V0 vs0) (hb1 : IsListBasis V1 vs1)
    (f : V0.carrier →ₗ[ℝ] V1.carrier) :
    hb1.coordMatrix hb0
        (LinearMap.mooreInv V0.innerIsIP V1.innerIsIP f) =
      matrixGSVDPinv (hb0.coordMatrix hb1 f)
        (IsListBasis.gram V0 vs0) (IsListBasis.gram V1 vs1) := by
  classical
  let A := hb0.coordMatrix hb1 f
  let MW := IsListBasis.gram V0 vs0
  let MV := IsListBasis.gram V1 vs1
  let gs := matrixGSVD A MW MV
  let G := matrixGSVDPinv A MW MV
  let g : V1.carrier →ₗ[ℝ] V0.carrier :=
    Matrix.toLin hb1.toBasis hb0.toBasis G
  have hGMatrix : LinearMap.toMatrix hb1.toBasis hb0.toBasis g = G :=
    LinearMap.toMatrix_toLin hb1.toBasis hb0.toBasis G
  have hfMatrix : LinearMap.toMatrix hb0.toBasis hb1.toBasis f = A := rfl
  have hG : G = gs.U * gs.sInvMat * gs.V.transpose * MV := by rfl
  have hfac : A = gs.V * gs.sMat * gs.U.transpose * MW := by
    simpa only [gs, GSVDecomposition.sMat] using
      matrixGSVD_factor A MW MV hb0.gram_posDef hb1.gram_posDef
  have hU : gs.U.transpose * MW * gs.U = 1 := by
    simpa only [gs] using
      matrixGSVD_U_orth A MW MV hb0.gram_posDef hb1.gram_posDef
  have hV : gs.V.transpose * MV * gs.V = 1 := by
    simpa only [gs] using
      matrixGSVD_V_orth A MW MV hb0.gram_posDef hb1.gram_posDef
  have hSSi : gs.sMat * gs.sInvMat = 1 := gs.sMat_mul_sInvMat
  have hSiS : gs.sInvMat * gs.sMat = 1 := gs.sInvMat_mul_sMat
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
  have hMV : MV.transpose = MV := by
    have h := IsListBasis.gram_isHermitian V1 vs1
    rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at h
    exact h
  have hMW : MW.transpose = MW := by
    have h := IsListBasis.gram_isHermitian V0 vs0
    rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at h
    exact h
  have hAGSelf : (A * G).transpose * MV = MV * (A * G) := by
    rw [hAG]
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hMV]
    noncomm_ring
  have hGASelf : (G * A).transpose * MW = MW * (G * A) := by
    rw [hGA]
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hMW]
    noncomm_ring
  have hfgMatrix : hb1.coordMatrix hb1 (f.comp g) = A * G := by
    simp only [IsListBasis.coordMatrix]
    rw [LinearMap.toMatrix_comp hb1.toBasis hb0.toBasis hb1.toBasis,
      hGMatrix, hfMatrix]
  have hgfMatrix : hb0.coordMatrix hb0 (g.comp f) = G * A := by
    simp only [IsListBasis.coordMatrix]
    rw [LinearMap.toMatrix_comp hb0.toBasis hb1.toBasis hb0.toBasis,
      hGMatrix, hfMatrix]
  have hfgf : (f.comp g).comp f = f := by
    apply (LinearMap.toMatrix hb0.toBasis hb1.toBasis).injective
    rw [LinearMap.toMatrix_comp hb0.toBasis hb1.toBasis hb1.toBasis,
      LinearMap.toMatrix_comp hb1.toBasis hb0.toBasis hb1.toBasis,
      hGMatrix, hfMatrix]
    exact hMP1
  have hgfg : (g.comp f).comp g = g := by
    apply (LinearMap.toMatrix hb1.toBasis hb0.toBasis).injective
    rw [LinearMap.toMatrix_comp hb1.toBasis hb0.toBasis hb0.toBasis,
      LinearMap.toMatrix_comp hb0.toBasis hb1.toBasis hb0.toBasis,
      hGMatrix, hfMatrix]
    exact hMP2
  have hfgSelf : ∀ x y,
      V1.innerProduct (f (g x)) y = V1.innerProduct x (f (g y)) := by
    simpa only [LinearMap.comp_apply] using
      hb1.innerProduct_self_of_coordMatrix (f.comp g) (A * G)
        hfgMatrix hAGSelf
  have hgfSelf : ∀ x y,
      V0.innerProduct (g (f x)) y = V0.innerProduct x (g (f y)) := by
    simpa only [LinearMap.comp_apply] using
      hb0.innerProduct_self_of_coordMatrix (g.comp f) (G * A)
        hgfMatrix hGASelf
  have hg : g = LinearMap.mooreInv V0.innerIsIP V1.innerIsIP f :=
    LinearMap.eq_mooreInv_of_penrose V0.innerIsIP V1.innerIsIP
      f g hfgf hgfg hfgSelf hgfSelf
  rw [← hg]
  exact hGMatrix

/-- Column form of the generalized-coordinate bridge. -/
theorem IsListBasis.mooreInv_apply_eq_matrixGSVDPinv_sum
    {V0 V1 : HSpace} {vs0 : List V0.carrier} {vs1 : List V1.carrier}
    (hb0 : IsListBasis V0 vs0) (hb1 : IsListBasis V1 vs1)
    (f : V0.carrier →ₗ[ℝ] V1.carrier) (i : Fin vs1.length) :
    LinearMap.mooreInv V0.innerIsIP V1.innerIsIP f (vs1.get i) =
      ∑ j : Fin vs0.length,
        matrixGSVDPinv (hb0.coordMatrix hb1 f)
          (IsListBasis.gram V0 vs0) (IsListBasis.gram V1 vs1) j i •
          vs0.get j := by
  have hmatrix := hb0.coordMatrix_mooreInv_eq_matrixGSVDPinv hb1 f
  rw [← hb0.sum_coords_smul
    (LinearMap.mooreInv V0.innerIsIP V1.innerIsIP f (vs1.get i))]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  have hentry := congrArg (fun M => M j i) hmatrix
  simpa only [IsListBasis.coords, IsListBasis.coordMatrix,
    LinearMap.toMatrix_apply, IsListBasis.toBasis_apply] using hentry

/-- Tensor form used by generalized-pseudoinverse term adequacy. -/
theorem IsListBasis.pinvTensor_eq_matrixGSVDPinv_sum
    {V0 V1 : HSpace} {vs0 : List V0.carrier} {vs1 : List V1.carrier}
    (hb0 : IsListBasis V0 vs0) (hb1 : IsListBasis V1 vs1)
    (f : V0.carrier →ₗ[ℝ] V1.carrier) :
    (dualTensorHomEquiv ℝ V1.carrier V0.carrier).symm
        (LinearMap.mooreInv V0.innerIsIP V1.innerIsIP f) =
      ∑ i : Fin vs1.length, ∑ j : Fin vs0.length,
        matrixGSVDPinv (hb0.coordMatrix hb1 f)
          (IsListBasis.gram V0 vs0) (IsListBasis.gram V1 vs1) j i •
          (V1.dualVec vs1 i ⊗ₜ[ℝ] vs0.get j) := by
  exact hb1.dualTensorHomEquiv_symm_eq_sum₂
    (LinearMap.mooreInv V0.innerIsIP V1.innerIsIP f)
    (fun j i => matrixGSVDPinv (hb0.coordMatrix hb1 f)
      (IsListBasis.gram V0 vs0) (IsListBasis.gram V1 vs1) i j)
    (hb0.mooreInv_apply_eq_matrixGSVDPinv_sum hb1 f)

end GLang
