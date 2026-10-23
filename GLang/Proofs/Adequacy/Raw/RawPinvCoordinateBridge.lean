import GLang.Numerics.SVD.ValueSVDBridge
import GLang.Proofs.Basis.BasisSoundness
import GLang.Numerics.Pseudoinverse.MoorePenroseChar
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Standard-coordinate pseudo-inverse bridge

This module connects the flat, row-major `matrixSVDPinv` used by the value
semantics with the intrinsic `LinearMap.mooreInv` used by the source
semantics.  The bridge is stated for arbitrary finite list bases whose Gram
matrices are the identity; the term adequacy rules obtain exactly those
hypotheses from `Basis.isStd`.
-/

namespace GLang

open scoped Matrix

/-- The four Moore--Penrose equations characterize the intrinsic
pseudo-inverse.  The final two hypotheses spell self-adjointness directly in
the supplied bilinear forms, avoiding any extra typeclass assumptions in the
statement. -/
theorem LinearMap.eq_mooreInv_of_penrose
    {V0 V1 : Type}
    [AddCommGroup V0] [Module ℝ V0] [FiniteDimensional ℝ V0]
    [AddCommGroup V1] [Module ℝ V1] [FiniteDimensional ℝ V1]
    {B0 : V0 →ₗ[ℝ] V0 →ₗ[ℝ] ℝ} (hB0 : IsInnerProduct B0)
    {B1 : V1 →ₗ[ℝ] V1 →ₗ[ℝ] ℝ} (hB1 : IsInnerProduct B1)
    (f : V0 →ₗ[ℝ] V1) (g : V1 →ₗ[ℝ] V0)
    (hfgf : (f.comp g).comp f = f)
    (hgfg : (g.comp f).comp g = g)
    (hfgSelf : ∀ x y, B1 (f (g x)) y = B1 x (f (g y)))
    (hgfSelf : ∀ x y, B0 (g (f x)) y = B0 x (g (f y))) :
    g = LinearMap.mooreInv hB0 hB1 f := by
  letI core0 : InnerProductSpace.Core ℝ V0 := hB0.toIPSCore
  letI core1 : InnerProductSpace.Core ℝ V1 := hB1.toIPSCore
  letI nag0 : NormedAddCommGroup V0 :=
    InnerProductSpace.Core.toNormedAddCommGroup (cd := core0)
  letI nag1 : NormedAddCommGroup V1 :=
    InnerProductSpace.Core.toNormedAddCommGroup (cd := core1)
  letI ips0 : InnerProductSpace ℝ V0 := InnerProductSpace.ofCore inferInstance
  letI ips1 : InnerProductSpace ℝ V1 := InnerProductSpace.ofCore inferInstance
  apply LinearMap.ext
  intro y
  have hfgfAt (x : V0) : f (g (f x)) = f x := by
    have h := LinearMap.congr_fun hfgf x
    simpa only [LinearMap.comp_apply] using h
  have hgfgAt (x : V1) : g (f (g x)) = g x := by
    have h := LinearMap.congr_fun hgfg x
    simpa only [LinearMap.comp_apply] using h
  have hgPerp : g y ∈ (LinearMap.ker f)ᗮ := by
    rw [Submodule.mem_orthogonal]
    intro x hx
    have hself := hgfSelf x (g y)
    simp only [show f x = 0 from hx, map_zero, LinearMap.zero_apply,
      hgfgAt] at hself
    exact hself.symm
  have hresPerp : y - f (g y) ∈ (LinearMap.range f)ᗮ := by
    rw [Submodule.mem_orthogonal]
    intro z hz
    obtain ⟨x, rfl⟩ := hz
    have hself := hfgSelf (f x) y
    rw [hfgfAt] at hself
    change B1 (f x) (y - f (g y)) = 0
    rw [map_sub, hself, sub_self]
  have hproj : f (g y) = (LinearMap.range f).starProjection y := by
    exact (Submodule.eq_starProjection_of_mem_orthogonal
      (LinearMap.mem_range_self f (g y)) hresPerp).symm
  let mi := LinearMap.mooreInv hB0 hB1 f
  have hmiPerp : mi y ∈ (LinearMap.ker f)ᗮ :=
    LinearMap.mooreInv_mem_ker_orthogonal hB0 hB1 f y
  have hmiProj : f (mi y) = (LinearMap.range f).starProjection y :=
    LinearMap.mooreInv_image_eq_starProjection hB0 hB1 f y
  have hdiffKer : g y - mi y ∈ LinearMap.ker f := by
    rw [LinearMap.mem_ker, map_sub, hproj, hmiProj, sub_self]
  have hdiffPerp : g y - mi y ∈ (LinearMap.ker f)ᗮ :=
    Submodule.sub_mem _ hgPerp hmiPerp
  have hzero : g y - mi y = 0 := by
    apply hB0.2.2
    exact (Submodule.mem_orthogonal _ _).mp hdiffPerp _ hdiffKer
  exact sub_eq_zero.mp hzero

/-- In orthonormal list bases, the intrinsic Moore inverse has exactly the
transpose of the row-major SVD pseudo-inverse used by the value semantics.
The input to `matrixSVDPinv` is transposed because source tensors store a
linear map by domain-major (row-major) coefficients. -/
theorem IsListBasis.coordMatrix_mooreInv_eq_matrixSVDPinv_transpose
    {V0 V1 : HSpace} {vs0 : List V0.carrier} {vs1 : List V1.carrier}
    (hb0 : IsListBasis V0 vs0) (hb1 : IsListBasis V1 vs1)
    (horth0 : ∀ i j : Fin vs0.length,
      V0.innerProduct (vs0.get i) (vs0.get j) = if i = j then 1 else 0)
    (horth1 : ∀ i j : Fin vs1.length,
      V1.innerProduct (vs1.get i) (vs1.get j) = if i = j then 1 else 0)
    (f : V0.carrier →ₗ[ℝ] V1.carrier) :
    hb1.coordMatrix hb0
        (LinearMap.mooreInv V0.innerIsIP V1.innerIsIP f) =
      (matrixSVDPinv (hb0.coordMatrix hb1 f).transpose).transpose := by
  classical
  letI core0 : InnerProductSpace.Core ℝ V0.carrier := V0.innerIsIP.toIPSCore
  letI core1 : InnerProductSpace.Core ℝ V1.carrier := V1.innerIsIP.toIPSCore
  letI nag0 : NormedAddCommGroup V0.carrier :=
    InnerProductSpace.Core.toNormedAddCommGroup (cd := core0)
  letI nag1 : NormedAddCommGroup V1.carrier :=
    InnerProductSpace.Core.toNormedAddCommGroup (cd := core1)
  letI ips0 : InnerProductSpace ℝ V0.carrier := InnerProductSpace.ofCore inferInstance
  letI ips1 : InnerProductSpace ℝ V1.carrier := InnerProductSpace.ofCore inferInstance
  have hon0 : Orthonormal ℝ hb0.toBasis := by
    rw [orthonormal_iff_ite]
    intro i j
    simpa only [IsListBasis.toBasis_apply] using horth0 i j
  have hon1 : Orthonormal ℝ hb1.toBasis := by
    rw [orthonormal_iff_ite]
    intro i j
    simpa only [IsListBasis.toBasis_apply] using horth1 i j
  let ob0 := hb0.toBasis.toOrthonormalBasis hon0
  let ob1 := hb1.toBasis.toOrthonormalBasis hon1
  let A := hb0.coordMatrix hb1 f
  let R := matrixSVDPinv A.transpose
  let G := R.transpose
  let g : V1.carrier →ₗ[ℝ] V0.carrier :=
    Matrix.toLin hb1.toBasis hb0.toBasis G
  have hgMatrix : LinearMap.toMatrix hb1.toBasis hb0.toBasis g = G := by
    exact LinearMap.toMatrix_toLin hb1.toBasis hb0.toBasis G
  have hfMatrix : LinearMap.toMatrix hb0.toBasis hb1.toBasis f = A := rfl
  have hMP1 : A * G * A = A := by
    have h := congrArg Matrix.transpose
      (matrixSVDPinv_mul_self A.transpose)
    simpa only [G, R, Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.mul_assoc] using h
  have hMP2 : G * A * G = G := by
    have h := congrArg Matrix.transpose
      (matrixSVDPinv_mul_self_mul_svdPinv A.transpose)
    simpa only [G, R, Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.mul_assoc] using h
  have hAGsymm : (A * G).transpose = A * G := by
    have h := (matrixSVDPinv_symm_properties A.transpose).2
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose] using h.symm
  have hGAsymm : (G * A).transpose = G * A := by
    have h := (matrixSVDPinv_symm_properties A.transpose).1
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose] using h.symm
  have hfgf : (f.comp g).comp f = f := by
    apply (LinearMap.toMatrix hb0.toBasis hb1.toBasis).injective
    rw [LinearMap.toMatrix_comp hb0.toBasis hb1.toBasis hb1.toBasis,
      LinearMap.toMatrix_comp hb1.toBasis hb0.toBasis hb1.toBasis,
      hgMatrix, hfMatrix]
    exact hMP1
  have hgfg : (g.comp f).comp g = g := by
    apply (LinearMap.toMatrix hb1.toBasis hb0.toBasis).injective
    rw [LinearMap.toMatrix_comp hb1.toBasis hb0.toBasis hb0.toBasis,
      LinearMap.toMatrix_comp hb0.toBasis hb1.toBasis hb0.toBasis,
      hgMatrix, hfMatrix]
    exact hMP2
  have hfgAdj : LinearMap.adjoint (f.comp g) = f.comp g := by
    apply (LinearMap.toMatrix ob1.toBasis ob1.toBasis).injective
    rw [LinearMap.toMatrix_adjoint ob1 ob1]
    dsimp only [ob1]
    rw [Module.Basis.toBasis_toOrthonormalBasis]
    rw [Matrix.conjTranspose_eq_transpose_of_trivial,
      LinearMap.toMatrix_comp hb1.toBasis hb0.toBasis hb1.toBasis,
      hgMatrix, hfMatrix]
    exact hAGsymm
  have hgfAdj : LinearMap.adjoint (g.comp f) = g.comp f := by
    apply (LinearMap.toMatrix ob0.toBasis ob0.toBasis).injective
    rw [LinearMap.toMatrix_adjoint ob0 ob0]
    dsimp only [ob0]
    rw [Module.Basis.toBasis_toOrthonormalBasis]
    rw [Matrix.conjTranspose_eq_transpose_of_trivial,
      LinearMap.toMatrix_comp hb0.toBasis hb1.toBasis hb0.toBasis,
      hgMatrix, hfMatrix]
    exact hGAsymm
  have hfgSelf : ∀ x y,
      V1.innerProduct (f (g x)) y = V1.innerProduct x (f (g y)) := by
    intro x y
    change @inner ℝ V1.carrier _ (f (g x)) y =
      @inner ℝ V1.carrier _ x (f (g y))
    simpa only [hfgAdj, LinearMap.comp_apply] using
      (LinearMap.adjoint_inner_left (f.comp g) y x)
  have hgfSelf : ∀ x y,
      V0.innerProduct (g (f x)) y = V0.innerProduct x (g (f y)) := by
    intro x y
    change @inner ℝ V0.carrier _ (g (f x)) y =
      @inner ℝ V0.carrier _ x (g (f y))
    simpa only [hgfAdj, LinearMap.comp_apply] using
      (LinearMap.adjoint_inner_left (g.comp f) y x)
  have hg : g = LinearMap.mooreInv V0.innerIsIP V1.innerIsIP f :=
    LinearMap.eq_mooreInv_of_penrose V0.innerIsIP V1.innerIsIP
      f g hfgf hgfg hfgSelf hgfSelf
  rw [← hg]
  exact hgMatrix

/-- Column form of the standard-coordinate bridge.  The row `i` emitted by
the flat pseudo-inverse is the expansion of the intrinsic inverse applied to
the `i`th vector of the original codomain basis. -/
theorem IsListBasis.mooreInv_apply_eq_matrixSVDPinv_sum
    {V0 V1 : HSpace} {vs0 : List V0.carrier} {vs1 : List V1.carrier}
    (hb0 : IsListBasis V0 vs0) (hb1 : IsListBasis V1 vs1)
    (horth0 : ∀ i j : Fin vs0.length,
      V0.innerProduct (vs0.get i) (vs0.get j) = if i = j then 1 else 0)
    (horth1 : ∀ i j : Fin vs1.length,
      V1.innerProduct (vs1.get i) (vs1.get j) = if i = j then 1 else 0)
    (f : V0.carrier →ₗ[ℝ] V1.carrier) (i : Fin vs1.length) :
    LinearMap.mooreInv V0.innerIsIP V1.innerIsIP f (vs1.get i) =
      ∑ j : Fin vs0.length,
        matrixSVDPinv (hb0.coordMatrix hb1 f).transpose i j • vs0.get j := by
  have hmatrix := hb0.coordMatrix_mooreInv_eq_matrixSVDPinv_transpose hb1
    horth0 horth1 f
  rw [← hb0.sum_coords_smul
    (LinearMap.mooreInv V0.innerIsIP V1.innerIsIP f (vs1.get i))]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  have hentry := congrArg (fun M => M j i) hmatrix
  simpa only [IsListBasis.coords, IsListBasis.coordMatrix,
    LinearMap.toMatrix_apply, IsListBasis.toBasis_apply,
    Matrix.transpose_apply] using hentry

/-- Tensor form used directly by the source/value agreement proof. -/
theorem IsListBasis.pinvTensor_eq_matrixSVDPinv_sum
    {V0 V1 : HSpace} {vs0 : List V0.carrier} {vs1 : List V1.carrier}
    (hb0 : IsListBasis V0 vs0) (hb1 : IsListBasis V1 vs1)
    (horth0 : ∀ i j : Fin vs0.length,
      V0.innerProduct (vs0.get i) (vs0.get j) = if i = j then 1 else 0)
    (horth1 : ∀ i j : Fin vs1.length,
      V1.innerProduct (vs1.get i) (vs1.get j) = if i = j then 1 else 0)
    (f : V0.carrier →ₗ[ℝ] V1.carrier) :
    (dualTensorHomEquiv ℝ V1.carrier V0.carrier).symm
        (LinearMap.mooreInv V0.innerIsIP V1.innerIsIP f) =
      ∑ i : Fin vs1.length, ∑ j : Fin vs0.length,
        matrixSVDPinv (hb0.coordMatrix hb1 f).transpose i j •
          (V1.dualVec vs1 i ⊗ₜ[ℝ] vs0.get j) := by
  exact hb1.dualTensorHomEquiv_symm_eq_sum₂
    (LinearMap.mooreInv V0.innerIsIP V1.innerIsIP f)
    (fun i j => matrixSVDPinv (hb0.coordMatrix hb1 f).transpose i j)
    (hb0.mooreInv_apply_eq_matrixSVDPinv_sum hb1 horth0 horth1 f)

end GLang
