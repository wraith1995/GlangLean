import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! Paired singular vectors from the spectral theorem, independently of the
project's numerical existence interfaces. These statements establish the
pairing that independently chosen canonical domain/codomain bases lack. -/
namespace GLang.GSVDPairedSpectral
noncomputable section
open scoped BigOperators RealInnerProductSpace

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

/-- Positive Gram eigenvectors determine codomain vectors by the required
literal pairing `v_i = A u_i / σ_i`. -/
def pairedImage (A : E →ₗ[ℝ] F) (u : E) (σ : ℝ) : F := σ⁻¹ • A u

theorem image_inner_of_gram_eigenvectors {ι : Type*} [DecidableEq ι] (A : E →ₗ[ℝ] F)
    (u : ι → E) (μ : ι → ℝ) (hu : Orthonormal ℝ u)
    (hμ : ∀ i, (LinearMap.adjoint A) (A (u i)) = μ i • u i) (i j : ι) :
    ⟪A (u i), A (u j)⟫ = μ j * (if i = j then 1 else 0) := by
  rw [← A.adjoint_inner_right, hμ, real_inner_smul_right, orthonormal_iff_ite.mp hu]

/-- Normalizing a positive Gram eigenfamily gives an orthonormal paired
codomain family; repeated singular values require no independent choices. -/
theorem pairedImage_orthonormal {ι : Type*} (A : E →ₗ[ℝ] F)
    (u : ι → E) (σ : ι → ℝ) (hu : Orthonormal ℝ u)
    (hσ : ∀ i, 0 < σ i)
    (heig : ∀ i, (LinearMap.adjoint A) (A (u i)) = (σ i)^2 • u i) :
    Orthonormal ℝ (fun i => pairedImage A (u i) (σ i)) := by
  classical
  rw [orthonormal_iff_ite]
  intro i j
  rw [pairedImage, pairedImage, real_inner_smul_left, real_inner_smul_right,
    image_inner_of_gram_eigenvectors A u (fun i => (σ i)^2) hu heig]
  by_cases hij : i = j
  · subst j
    simp only [ite_true]
    field_simp [ne_of_gt (hσ i)]
  · simp [hij]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem apply_eq_sigma_pairedImage (A : E →ₗ[ℝ] F) (u : E) (σ : ℝ) (hσ : σ ≠ 0) :
    A u = σ • pairedImage A u σ := by
  simp [pairedImage, smul_smul, hσ]

theorem adjoint_pairedImage (A : E →ₗ[ℝ] F) (u : E) (σ : ℝ) (hσ : σ ≠ 0)
    (heig : (LinearMap.adjoint A) (A u) = σ^2 • u) :
    (LinearMap.adjoint A) (pairedImage A u σ) = σ • u := by
  simp only [pairedImage, map_smul, heig, smul_smul]
  congr 1
  field_simp

/-- Zero Gram eigenvectors are precisely killed by the original map. -/
theorem apply_eq_zero_of_gram_eq_zero (A : E →ₗ[ℝ] F) (u : E)
    (hu : (LinearMap.adjoint A) (A u) = 0) : A u = 0 := by
  apply (inner_self_eq_zero (𝕜 := ℝ)).mp
  rw [← A.adjoint_inner_right, hu, inner_zero_right]

/-- The squared singular value associated with a unit Gram eigenvector is
nonnegative, as its value is the squared norm of the image. -/
theorem gram_eigenvalue_nonneg (A : E →ₗ[ℝ] F) (u : E) (μ : ℝ)
    (hu : ⟪u, u⟫ = 1) (heig : (LinearMap.adjoint A) (A u) = μ • u) :
    0 ≤ μ := by
  have hh : ⟪A u, A u⟫ = μ := by
    rw [← A.adjoint_inner_right, heig, real_inner_smul_right, hu, mul_one]
  rw [← hh]
  exact real_inner_self_nonneg

/-- Mathlib's ordered Gram eigenbasis, not an independently chosen image basis. -/
def gramBasis (A : E →ₗ[ℝ] F) :
    OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ E :=
  A.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl

def gramValues (A : E →ₗ[ℝ] F) : Fin (Module.finrank ℝ E) → ℝ :=
  A.isSymmetric_adjoint_comp_self.eigenvalues rfl

def singularValues (A : E →ₗ[ℝ] F) (i : Fin (Module.finrank ℝ E)) : ℝ :=
  Real.sqrt (gramValues A i)

theorem gramBasis_eigen (A : E →ₗ[ℝ] F) (i : Fin (Module.finrank ℝ E)) :
    (LinearMap.adjoint A) (A (gramBasis A i)) = gramValues A i • gramBasis A i :=
  A.isSymmetric_adjoint_comp_self.apply_eigenvectorBasis rfl i

theorem gramValues_nonneg (A : E →ₗ[ℝ] F) (i : Fin (Module.finrank ℝ E)) :
    0 ≤ gramValues A i := by
  apply gram_eigenvalue_nonneg A (gramBasis A i) _ _ (gramBasis_eigen A i)
  simp

theorem singularValues_antitone (A : E →ₗ[ℝ] F) : Antitone (singularValues A) := by
  intro i j hij
  exact Real.sqrt_le_sqrt (A.isSymmetric_adjoint_comp_self.eigenvalues_antitone rfl hij)

/-- Keep exactly the positive singular directions; zero eigenvalues belong to the kernel. -/
def PositiveIndex (A : E →ₗ[ℝ] F) := {i : Fin (Module.finrank ℝ E) // 0 < gramValues A i}

theorem positive_paired_orthonormal (A : E →ₗ[ℝ] F) :
    Orthonormal ℝ (fun i : PositiveIndex A =>
      pairedImage A (gramBasis A i.val) (singularValues A i.val)) := by
  apply pairedImage_orthonormal A (fun i : PositiveIndex A => gramBasis A i.val)
    (fun i : PositiveIndex A => singularValues A i.val)
  · exact (gramBasis A).orthonormal.comp _ Subtype.val_injective
  · intro i
    exact Real.sqrt_pos.mpr i.property
  · intro i
    rw [singularValues, Real.sq_sqrt (gramValues_nonneg A i.val)]
    exact gramBasis_eigen A i.val

/-- Including zero directions with zero coefficient makes reconstruction a
sum over the entire ordered domain eigenbasis, avoiding any enumeration choice. -/
theorem apply_gramBasis_eq_sigma_paired (A : E →ₗ[ℝ] F)
    (i : Fin (Module.finrank ℝ E)) :
    A (gramBasis A i) = singularValues A i •
      pairedImage A (gramBasis A i) (singularValues A i) := by
  by_cases hz : gramValues A i = 0
  · have ha : A (gramBasis A i) = 0 :=
      apply_eq_zero_of_gram_eq_zero A _ (by simp [gramBasis_eigen, hz])
    simp [ha, pairedImage]
  · exact apply_eq_sigma_pairedImage A _ _
      (ne_of_gt (Real.sqrt_pos.mpr (lt_of_le_of_ne (gramValues_nonneg A i) (Ne.symm hz))))

/-- The actual spectral singular expansion, with the paired image vectors.
This is the Hilbert-space form of `A = V diag(σ) U*`. -/
theorem spectral_reconstruction (A : E →ₗ[ℝ] F) (x : E) :
    A x = ∑ i : Fin (Module.finrank ℝ E),
      (⟪gramBasis A i, x⟫ * singularValues A i) •
        pairedImage A (gramBasis A i) (singularValues A i) := by
  conv_lhs => rw [← (gramBasis A).sum_repr' x]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul, apply_gramBasis_eq_sigma_paired, smul_smul]

/-- The paired positive family spans the whole image; no codomain spectral
basis needs to be chosen or matched independently. -/
theorem positive_paired_span (A : E →ₗ[ℝ] F) :
    Submodule.span ℝ (Set.range (fun i : PositiveIndex A =>
      pairedImage A (gramBasis A i.val) (singularValues A i.val))) =
      LinearMap.range A := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact ⟨(singularValues A i.val)⁻¹ • gramBasis A i.val, by simp [pairedImage]⟩
  · rintro _ ⟨x, rfl⟩
    rw [spectral_reconstruction]
    apply Submodule.sum_mem
    intro i _
    by_cases hz : gramValues A i = 0
    · simp [singularValues, hz]
    · apply Submodule.smul_mem
      apply Submodule.subset_span
      exact ⟨⟨i, lt_of_le_of_ne (gramValues_nonneg A i) (Ne.symm hz)⟩, rfl⟩

end
end GLang.GSVDPairedSpectral
