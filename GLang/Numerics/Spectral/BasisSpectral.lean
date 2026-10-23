import GLang.Numerics.RREF.BasisLexInd
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.Adjoint

namespace GLang.BasisSpectral
noncomputable def normalizedLexInd (V : HSpace) (xs : List V.carrier) :=
  letI := V.innerIsIP.toIPSCore
  letI : NormedAddCommGroup V.carrier := V.innerIsIP.toIPSCore.toNormedAddCommGroup
  letI : InnerProductSpace ℝ V.carrier := InnerProductSpace.ofCore inferInstance
  List.ofFn (InnerProductSpace.gramSchmidtNormed ℝ (V.lexInd xs).get)

theorem normalizedLexInd_orthonormal (V : HSpace) (xs : List V.carrier) :
    letI := V.innerIsIP.toIPSCore
    letI : NormedAddCommGroup V.carrier := V.innerIsIP.toIPSCore.toNormedAddCommGroup
    letI : InnerProductSpace ℝ V.carrier := InnerProductSpace.ofCore inferInstance
    Orthonormal ℝ (InnerProductSpace.gramSchmidtNormed ℝ (V.lexInd xs).get) := by
  letI := V.innerIsIP.toIPSCore
  letI : NormedAddCommGroup V.carrier := V.innerIsIP.toIPSCore.toNormedAddCommGroup
  letI : InnerProductSpace ℝ V.carrier := InnerProductSpace.ofCore inferInstance
  exact InnerProductSpace.gramSchmidtNormed_orthonormal (V.lexInd_linearly_independent xs)

theorem normalizedLexInd_span (V : HSpace) (xs : List V.carrier) :
    letI := V.innerIsIP.toIPSCore
    letI : NormedAddCommGroup V.carrier := V.innerIsIP.toIPSCore.toNormedAddCommGroup
    letI : InnerProductSpace ℝ V.carrier := InnerProductSpace.ofCore inferInstance
    Submodule.span ℝ (Set.range (InnerProductSpace.gramSchmidtNormed ℝ (V.lexInd xs).get)) =
      Submodule.span ℝ {v | v ∈ xs} := by
  letI := V.innerIsIP.toIPSCore
  letI : NormedAddCommGroup V.carrier := V.innerIsIP.toIPSCore.toNormedAddCommGroup
  letI : InnerProductSpace ℝ V.carrier := InnerProductSpace.ofCore inferInstance
  rw [InnerProductSpace.span_gramSchmidtNormed_range, InnerProductSpace.span_gramSchmidt,
    HSpace.lexInd_span_eq, ← HSpace.span_setOf_mem_eq_span_range_get]

variable {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]
noncomputable def eigenvaluesIncreasing (A : E →ₗ[ℝ] F) : List ℝ :=
  (Finset.univ.image (A.isSymmetric_adjoint_comp_self.eigenvalues rfl)).sort (· ≤ ·)
noncomputable def spectralProjector (S : E →ₗ[ℝ] E) (μ : ℝ) : E →ₗ[ℝ] E :=
  (Module.End.eigenspace S μ).starProjection.toLinearMap

noncomputable def bucket (V : HSpace) (S : V.carrier →ₗ[ℝ] V.carrier)
    (μ : ℝ) (xs : List V.carrier) : List V.carrier :=
  letI := V.innerIsIP.toIPSCore
  letI : NormedAddCommGroup V.carrier := V.innerIsIP.toIPSCore.toNormedAddCommGroup
  letI : InnerProductSpace ℝ V.carrier := InnerProductSpace.ofCore inferInstance
  normalizedLexInd V (xs.map (spectralProjector S μ))

/-- Left spectral construction with the actual predicate evaluated on each
distinct eigenvalue, in increasing order. The live GSVD selection agrees with
this specification via `ValueCanonicalFSV.selectGSVD_eq_select`. -/
noncomputable def filteredLeft (V W : HSpace)
    (A : V.carrier →ₗ[ℝ] W.carrier) (pred : ℝ → Bool)
    (xs : List V.carrier) : List V.carrier :=
  letI := V.innerIsIP.toIPSCore
  letI : NormedAddCommGroup V.carrier := V.innerIsIP.toIPSCore.toNormedAddCommGroup
  letI : InnerProductSpace ℝ V.carrier := InnerProductSpace.ofCore inferInstance
  letI := W.innerIsIP.toIPSCore
  letI : NormedAddCommGroup W.carrier := W.innerIsIP.toIPSCore.toNormedAddCommGroup
  letI : InnerProductSpace ℝ W.carrier := InnerProductSpace.ofCore inferInstance
  ((eigenvaluesIncreasing A).filter pred).flatMap
    (fun μ => bucket V (LinearMap.adjoint A ∘ₗ A) μ xs)

/-- Right spectral construction with the actual predicate evaluated on each
distinct eigenvalue, in increasing order. The live GSVD selection agrees with
this specification via `ValueCanonicalFSV.selectGSVD_eq_select`. -/
noncomputable def filteredRight (V W : HSpace)
    (A : V.carrier →ₗ[ℝ] W.carrier) (pred : ℝ → Bool)
    (xs : List W.carrier) : List W.carrier :=
  letI := V.innerIsIP.toIPSCore
  letI : NormedAddCommGroup V.carrier := V.innerIsIP.toIPSCore.toNormedAddCommGroup
  letI : InnerProductSpace ℝ V.carrier := InnerProductSpace.ofCore inferInstance
  letI := W.innerIsIP.toIPSCore
  letI : NormedAddCommGroup W.carrier := W.innerIsIP.toIPSCore.toNormedAddCommGroup
  letI : InnerProductSpace ℝ W.carrier := InnerProductSpace.ofCore inferInstance
  ((eigenvaluesIncreasing (LinearMap.adjoint A)).filter pred).flatMap
    (fun μ => bucket W (A ∘ₗ LinearMap.adjoint A) μ xs)

end GLang.BasisSpectral
