import GLang.Numerics.Spectral.BasisSpectralTransport

/-! Exact ordered filtered singular-vector transport across isometric coordinates. -/
noncomputable section
namespace GLang.BasisSpectral
section Generic
variable {E F E' F' : Type}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup E'] [InnerProductSpace ℝ E'] [FiniteDimensional ℝ E']
  [NormedAddCommGroup F'] [InnerProductSpace ℝ F'] [FiniteDimensional ℝ F']

/-- Adjoint maps respect a pair of isometric coordinate changes. -/
theorem adjoint_intertwines (e : E ≃ₗᵢ[ℝ] E') (f : F ≃ₗᵢ[ℝ] F')
    (A : E →ₗ[ℝ] F) (B : E' →ₗ[ℝ] F')
    (h : ∀ x, B (e x) = f (A x)) (y : F) :
    LinearMap.adjoint B (f y) = e (LinearMap.adjoint A y) := by
  apply ext_inner_right ℝ
  intro z
  obtain ⟨x, rfl⟩ := e.surjective z
  rw [LinearMap.adjoint_inner_left, h, f.inner_map_map,
    e.inner_map_map, LinearMap.adjoint_inner_left]

/-- Gram operators respect the domain coordinate change. -/
theorem gram_intertwines (e : E ≃ₗᵢ[ℝ] E') (f : F ≃ₗᵢ[ℝ] F')
    (A : E →ₗ[ℝ] F) (B : E' →ₗ[ℝ] F')
    (h : ∀ x, B (e x) = f (A x)) (x : E) :
    (LinearMap.adjoint B ∘ₗ B) (e x) = e ((LinearMap.adjoint A ∘ₗ A) x) := by
  simp only [LinearMap.comp_apply, h, adjoint_intertwines e f A B h]

/-- Conjugacy preserves every eigenvalue, including zero. -/
theorem hasEigenvalue_intertwines (e : E ≃ₗ[ℝ] E')
    (S : E →ₗ[ℝ] E) (T : E' →ₗ[ℝ] E')
    (h : ∀ x, T (e x) = e (S x)) (μ : ℝ) :
    Module.End.HasEigenvalue T μ ↔ Module.End.HasEigenvalue S μ := by
  constructor
  · intro ht
    obtain ⟨y, hy⟩ := ht.exists_hasEigenvector
    apply Module.End.hasEigenvalue_of_hasEigenvector (x := e.symm y)
    constructor
    · rw [Module.End.mem_eigenspace_iff]
      apply e.injective
      rw [← h, e.apply_symm_apply, hy.apply_eq_smul, map_smul, e.apply_symm_apply]
    · simpa using hy.2
  · intro hs
    obtain ⟨x, hx⟩ := hs.exists_hasEigenvector
    apply Module.End.hasEigenvalue_of_hasEigenvector (x := e x)
    constructor
    · rw [Module.End.mem_eigenspace_iff, h, hx.apply_eq_smul, map_smul]
    · simpa using hx.2

/-- Distinct ascending spectral order is invariant, not merely its underlying set. -/
theorem eigenvaluesIncreasing_intertwines (e : E ≃ₗᵢ[ℝ] E') (f : F ≃ₗᵢ[ℝ] F')
    (A : E →ₗ[ℝ] F) (B : E' →ₗ[ℝ] F')
    (h : ∀ x, B (e x) = f (A x)) :
    eigenvaluesIncreasing B = eigenvaluesIncreasing A := by
  unfold eigenvaluesIncreasing
  congr 1
  ext μ
  have hm := (eigenvaluesIncreasing_mem_iff B μ).trans
    ((hasEigenvalue_intertwines e.toLinearEquiv _ _ (gram_intertwines e f A B h) μ).trans
      (eigenvaluesIncreasing_mem_iff A μ).symm)
  simpa only [eigenvaluesIncreasing, Finset.mem_sort] using hm
end Generic

section HSpaceTransport
variable {V W V' W' : HSpace}
local instance : InnerProductSpace.Core ℝ V.carrier := V.innerIsIP.toIPSCore
local instance : NormedAddCommGroup V.carrier := V.innerIsIP.toIPSCore.toNormedAddCommGroup
local instance : InnerProductSpace ℝ V.carrier := InnerProductSpace.ofCore inferInstance
local instance : InnerProductSpace.Core ℝ W.carrier := W.innerIsIP.toIPSCore
local instance : NormedAddCommGroup W.carrier := W.innerIsIP.toIPSCore.toNormedAddCommGroup
local instance : InnerProductSpace ℝ W.carrier := InnerProductSpace.ofCore inferInstance
local instance : InnerProductSpace.Core ℝ V'.carrier := V'.innerIsIP.toIPSCore
local instance : NormedAddCommGroup V'.carrier := V'.innerIsIP.toIPSCore.toNormedAddCommGroup
local instance : InnerProductSpace ℝ V'.carrier := InnerProductSpace.ofCore inferInstance
local instance : InnerProductSpace.Core ℝ W'.carrier := W'.innerIsIP.toIPSCore
local instance : NormedAddCommGroup W'.carrier := W'.innerIsIP.toIPSCore.toNormedAddCommGroup
local instance : InnerProductSpace ℝ W'.carrier := InnerProductSpace.ofCore inferInstance

/-- Exact filtered left lists commute with simultaneous isometric coordinates.
The predicate is evaluated at the same sorted eigenvalues on both sides. -/
theorem filteredLeft_map (e : V.carrier ≃ₗᵢ[ℝ] V'.carrier)
    (f : W.carrier ≃ₗᵢ[ℝ] W'.carrier)
    (A : V.carrier →ₗ[ℝ] W.carrier) (B : V'.carrier →ₗ[ℝ] W'.carrier)
    (h : ∀ x, B (e x) = f (A x)) (pred : ℝ → Bool) (xs : List V.carrier) :
    filteredLeft V' W' B pred (xs.map e) = (filteredLeft V W A pred xs).map e := by
  unfold filteredLeft
  rw [eigenvaluesIncreasing_intertwines e f A B h, List.map_flatMap]
  congr 1
  funext μ
  exact bucket_map e _ _ (gram_intertwines e f A B h) μ xs

/-- Exact filtered right lists commute with the same pair of coordinate changes. -/
theorem filteredRight_map (e : V.carrier ≃ₗᵢ[ℝ] V'.carrier)
    (f : W.carrier ≃ₗᵢ[ℝ] W'.carrier)
    (A : V.carrier →ₗ[ℝ] W.carrier) (B : V'.carrier →ₗ[ℝ] W'.carrier)
    (h : ∀ x, B (e x) = f (A x)) (pred : ℝ → Bool) (ys : List W.carrier) :
    filteredRight V' W' B pred (ys.map f) = (filteredRight V W A pred ys).map f := by
  have hh := filteredLeft_map f e (LinearMap.adjoint A) (LinearMap.adjoint B)
    (adjoint_intertwines e f A B h) pred ys
  simpa only [filteredLeft, filteredRight, LinearMap.adjoint_adjoint] using hh
end HSpaceTransport
end GLang.BasisSpectral
