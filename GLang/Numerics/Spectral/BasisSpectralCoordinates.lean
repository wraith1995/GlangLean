import GLang.Numerics.Spectral.BasisSpectralProperties

/-! # Exact coordinate conversion between independently chosen spectral bases

Rows index the target basis; columns index the source basis. This explicit
matrix retains signs, within-eigenspace rotations, and ordering changes that
a diagonal positive singular-value matrix cannot represent.
-/
noncomputable section
open scoped BigOperators Matrix
namespace GLang.BasisSpectral

section Coordinates
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {n m : ℕ}

/-- Orthogonal expansion of any vector in the span of a finite ON family. -/
theorem orthonormal_reconstruct (b : Fin n → E) (hb : Orthonormal ℝ b)
    {x : E} (hx : x ∈ Submodule.span ℝ (Set.range b)) :
    ∑ i, inner ℝ (b i) x • b i = x := by
  induction hx using Submodule.span_induction with
  | mem v hv =>
      obtain ⟨j, rfl⟩ := hv
      simp [orthonormal_iff_ite.mp hb]
  | zero => simp
  | add u v hu hv ihu ihv =>
      simp only [inner_add_right, add_smul, Finset.sum_add_distrib, ihu, ihv]
  | smul a v hv ih =>
      simp only [inner_smul_right, mul_smul, ← Finset.smul_sum, ih]

/-- Exact source-to-target coordinate matrix: target rows, source columns. -/
def transitionMatrix (target : Fin n → E) (source : Fin m → E) :
    Matrix (Fin n) (Fin m) ℝ :=
  fun i j => inner ℝ (target i) (source j)

theorem transitionMatrix_column (target : Fin n → E) (source : Fin m → E)
    (ht : Orthonormal ℝ target)
    (hs : ∀ j, source j ∈ Submodule.span ℝ (Set.range target)) (j : Fin m) :
    ∑ i, transitionMatrix target source i j • target i = source j :=
  orthonormal_reconstruct target ht (hs j)

/-- Matrix-vector conversion preserves the represented vector exactly. This
holds also for a nonorthonormal source family (e.g. an image basis). -/
theorem transitionMatrix_mulVec (target : Fin n → E) (source : Fin m → E)
    (ht : Orthonormal ℝ target)
    (hs : ∀ j, source j ∈ Submodule.span ℝ (Set.range target)) (a : Fin m → ℝ) :
    ∑ i, ((transitionMatrix target source) *ᵥ a) i • target i =
      ∑ j, a j • source j := by
  simp only [Matrix.mulVec, dotProduct, Finset.sum_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  calc
    ∑ i, (transitionMatrix target source i j * a j) • target i =
        a j • (∑ i, transitionMatrix target source i j • target i) := by
      simp only [Finset.smul_sum, ← mul_smul, mul_comm]
    _ = a j • source j := by rw [transitionMatrix_column target source ht hs j]

/-- If both families are ON, conversion has orthonormal columns. -/
theorem transitionMatrix_transpose_mul (target : Fin n → E) (source : Fin m → E)
    (ht : Orthonormal ℝ target) (hs : Orthonormal ℝ source)
    (hspan : ∀ j, source j ∈ Submodule.span ℝ (Set.range target)) :
    (transitionMatrix target source)ᵀ * transitionMatrix target source = 1 := by
  ext j k
  have h := congrArg (fun v => inner ℝ v (source k))
    (transitionMatrix_column target source ht hspan j)
  simp only [sum_inner, inner_smul_left, RCLike.conj_to_real, transitionMatrix] at h
  change (∑ i, inner ℝ (target i) (source j) * inner ℝ (target i) (source k)) = _
  rw [h]
  exact (orthonormal_iff_ite.mp hs j k).trans (Matrix.one_apply (i := j) (j := k)).symm

end Coordinates
end GLang.BasisSpectral
