import GLang.Numerics.Spectral.BasisSpectralProperties
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Eigenspace.Minpoly

noncomputable section
namespace GLang.BasisSpectral
open Polynomial
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Distinct spectral values of a symmetric operator. -/
def spectrumValues (S : E →ₗ[ℝ] E) (hS : S.IsSymmetric) : Finset ℝ :=
  Finset.univ.image (hS.eigenvalues rfl)

def projectorPolynomial (S : E →ₗ[ℝ] E) (hS : S.IsSymmetric) (μ : ℝ) : ℝ[X] :=
  Lagrange.basis (spectrumValues S hS) id μ

theorem projectorPolynomial_eq (S : E →ₗ[ℝ] E) (hS : S.IsSymmetric) (μ : ℝ)
    (hμ : Module.End.HasEigenvalue S μ) :
    aeval S (projectorPolynomial S hS μ) = spectralProjector S μ := by
  have hμmem : μ ∈ spectrumValues S hS := by
    obtain ⟨i, hi⟩ := hS.exists_eigenvalues_eq rfl hμ
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi⟩
  apply (hS.eigenvectorBasis rfl).toBasis.ext
  intro i
  change aeval S (projectorPolynomial S hS μ) (hS.eigenvectorBasis rfl i) = _
  rw [Module.End.aeval_apply_of_hasEigenvector (hS.hasEigenvector_eigenvectorBasis rfl i)]
  simp only [RCLike.ofReal_real_eq_id, id_eq, OrthonormalBasis.coe_toBasis]
  have hνmem : hS.eigenvalues rfl i ∈ spectrumValues S hS :=
    Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  by_cases he : μ = hS.eigenvalues rfl i
  · have hp : (projectorPolynomial S hS μ).eval (hS.eigenvalues rfl i) = 1 := by
      rw [← he]
      exact Lagrange.eval_basis_self (fun _ _ _ _ h => h) hμmem
    rw [hp, one_smul]
    exact (Submodule.starProjection_eq_self_iff.mpr
      (he.symm ▸ (hS.hasEigenvector_eigenvectorBasis rfl i).1)).symm
  · have hp : (projectorPolynomial S hS μ).eval (hS.eigenvalues rfl i) = 0 :=
      Lagrange.eval_basis_of_ne (v := id) he hνmem
    rw [hp, zero_smul]
    symm
    apply (Submodule.starProjection_apply_eq_zero_iff _).mpr
    rw [Submodule.mem_orthogonal]
    intro w hw
    exact hS.orthogonalFamily_eigenspaces he ⟨w, hw⟩
      ⟨_, (hS.hasEigenvector_eigenvectorBasis rfl i).1⟩

end GLang.BasisSpectral
