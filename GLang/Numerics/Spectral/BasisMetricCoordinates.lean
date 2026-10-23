import GLang.Numerics.Spectral.BasisSpectralMatrices
import GLang.Numerics.Spectral.BasisFSVGSVD

/-! # Ordered input-basis charts into metric coordinate spaces -/
noncomputable section
open scoped Matrix BigOperators
namespace GLang.BasisSpectral

section Chart
variable {V : HSpace} {xs : List V.carrier} (hb : IsListBasis V xs)
/-- Ordered basis coordinates are an isometry when equipped with their Gram
metric. This works for nonorthonormal input bases. -/
def coordinateChart :
  letI := V.innerIsIP.toIPSCore
  letI : NormedAddCommGroup V.carrier := V.innerIsIP.toIPSCore.toNormedAddCommGroup
  letI : InnerProductSpace ℝ V.carrier := InnerProductSpace.ofCore inferInstance
  let C := metricSpace (IsListBasis.gram V xs) hb.gram_posDef
  letI := C.innerIsIP.toIPSCore
  letI : NormedAddCommGroup (Fin xs.length → ℝ) := C.innerIsIP.toIPSCore.toNormedAddCommGroup
  letI : SeminormedAddCommGroup (Fin xs.length → ℝ) := C.innerIsIP.toIPSCore.toNormedAddCommGroup.toSeminormedAddCommGroup
  letI : InnerProductSpace ℝ (Fin xs.length → ℝ) := InnerProductSpace.ofCore inferInstance
  (Fin xs.length → ℝ) ≃ₗᵢ[ℝ] V.carrier := by
  letI := V.innerIsIP.toIPSCore
  letI : NormedAddCommGroup V.carrier := V.innerIsIP.toIPSCore.toNormedAddCommGroup
  letI : InnerProductSpace ℝ V.carrier := InnerProductSpace.ofCore inferInstance
  let C := metricSpace (IsListBasis.gram V xs) hb.gram_posDef
  letI := C.innerIsIP.toIPSCore
  letI : NormedAddCommGroup (Fin xs.length → ℝ) := C.innerIsIP.toIPSCore.toNormedAddCommGroup
  letI : SeminormedAddCommGroup (Fin xs.length → ℝ) := C.innerIsIP.toIPSCore.toNormedAddCommGroup.toSeminormedAddCommGroup
  letI : InnerProductSpace ℝ (Fin xs.length → ℝ) := InnerProductSpace.ofCore inferInstance
  exact hb.toBasis.equivFun.symm.isometryOfInner (by
    intro a b
    change V.innerProduct (hb.toBasis.equivFun.symm a) (hb.toBasis.equivFun.symm b) =
      Matrix.toBilin' (IsListBasis.gram V xs) a b
    rw [Module.Basis.equivFun_symm_apply, Module.Basis.equivFun_symm_apply]
    simp only [IsListBasis.toBasis_apply]
    exact (IsListBasis.innerProduct_sum_smul V xs a b).trans
      (Matrix.toBilin'_apply' _ _ _).symm)

theorem coordinateChart_apply (a : Fin xs.length → ℝ) :
    coordinateChart hb a = ∑ i, a i • xs.get i := by
  change hb.toBasis.equivFun.symm a = _
  simpa only [IsListBasis.toBasis_apply] using Module.Basis.equivFun_symm_apply hb.toBasis a

/-- The numeric coordinate axes are sent to the supplied basis in its exact
original order. -/
theorem coordinateChart_basis :
    (coordinateBasis xs.length).map (coordinateChart hb) = xs := by
  simp only [coordinateBasis, List.map_ofFn]
  convert List.ofFn_get xs using 1
  congr 1
  funext i
  simp only [Function.comp_apply]
  rw [coordinateChart_apply]
  simp [Pi.single_apply]
end Chart

/-- The coordinate matrix intertwines the two ordered metric charts exactly. -/
theorem coordinateChart_intertwines {V W : HSpace}
    {xs : List V.carrier} {ys : List W.carrier}
    (hb : IsListBasis V xs) (hc : IsListBasis W ys)
    (f : V.carrier →ₗ[ℝ] W.carrier) (a : Fin xs.length → ℝ) :
    coordinateChart hc (hb.coordMatrix hc f *ᵥ a) = f (coordinateChart hb a) := by
  rw [coordinateChart_apply, coordinateChart_apply]
  exact (hb.apply_sum_smul hc f a).symm

end GLang.BasisSpectral
